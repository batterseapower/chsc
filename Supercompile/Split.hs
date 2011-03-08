{-# LANGUAGE PatternGuards, ViewPatterns, TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable,
             MultiParamTypeClasses, FlexibleInstances, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (MonadStatics(..), split, generalise) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Deeds
import Evaluator.Evaluate (normalise)
import Evaluator.FreeVars
import Evaluator.Residualise
import Evaluator.Syntax

import Termination.Generaliser (Generaliser(..))

import Name
import Renaming
import StaticFlags
import Utilities hiding (tails)

import Algebra.Lattice

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntSet as IS


class Monad m => MonadStatics m where
    bindCapturedFloats :: FreeVars -> m a -> m (Out [(Var, FVedTerm)], a)


--
-- == Gathering entry information for the splitter ==
--

data Entered = Once Id -- ^ The Id is a context identifier: if a binding is Entered twice from the same context it's really a single Entrance
             | Many    -- ^ A result of anything other than Once (or None, represented implicitly) is uninteresting for optimisation purposes
             deriving (Eq, Show)

instance Pretty Entered where
    pPrint = text . show

instance JoinSemiLattice Entered where
    join = plusEntered

isOnce :: Entered -> Bool
isOnce (Once _) = True
isOnce _ = False

plusEntered :: Entered -> Entered -> Entered
plusEntered (Once id1) (Once id2)
  | id1 == id2 = Once id1
  | otherwise  = Many
plusEntered _ _ = Many


type EnteredEnv = M.Map (Out Var) Entered

mkEnteredEnv :: Entered -> FreeVars -> EnteredEnv
mkEnteredEnv = setToMap


--
-- == The splitter ==

-- Note [Phantom variables and bindings introduced by scrutinisation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- If we never introduced bindings from scrutinisation, the world of phantom bindings would be relatively
-- simple. In such a world, we would have this property:
--
--   The free variables of h-functions generated while supercompiling some term would never have
--   more free variables than the term being supercompiled
--
-- Unfortunately, this is not true in the real world. What can happen is this. We supercompile:
--  h1 x = case x of True -> e1; False -> e2
--
-- Which leads to the two recursively-supercompiled components:
--  h2 = let <x = True> in e1
--  h3 = let <x = False> in e2
--
-- Note that x was not static (free) in h1, but it is static (free) in h2. Thus, h-functions generated
-- during supercompilation (h2, h3) have more free variables than the term from which they were generated (h1).
--
--
-- Note [When to bind captured floats]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Ordinarily, we only need to check to see if we residualise some floating h-functions when we produce
-- a residual let-binding.  This is because in the normal course of things any binding that was originally
-- introduced as a lambda/alt-binding will never be made into a free variable of a final h-function.  However,
-- there are two situations which break this invariant:
--  1. We might choose to create a LetBound heap binding when driving the branches of a residual case expression
--     that scrutinises a free variable. This changes a LambdaBound thing into a LetBound one, so we need to be
--     careful to residualise the resulting h-function under that lambda-binder.
--
--     In fact, we used to do this but don't any more - see Note [Phantom variables and bindings introduced by scrutinisation]
--  2. More relevantly, we might implement an optimisation that prevents h-functions from being lambda-abstracted
--     over anything lambda-bound above a let-binding that we can see will trap the h-function under a let. For example,
--     when driving:
--
--       \x -> let f = \y -> ...
--             in D[<x |-> \lambda{}, f |-> l{\y -> ...} | ... f ... x ...>]
--
--     There is no point lambda-abstracting over x because we're going to have to drop the h-function under the f
--     binding anyway. To implement this we might drive with (x |-> l{}) instead, but once again this converts a
--     lambda-binding to a let-binding.
--
-- For this reason, we are careful to use bindCapturedFloats even when driving the arms of case expressions/bodies of lambdas.
--
--
-- Note [Bind captured floats fixed point]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Because bound h-functions (e.g. h2 or h3) may be referred to by other h-functions (e.g. h1) which do not
-- refer to any of the free variables of the h-functions we are about to bind, we have a fixed point in bindCapturedFloats.
-- This fixed point ensures we bind those h-functions that have as free variables any h-functions we are about to bind.


{-# INLINE split #-}
split :: MonadStatics m
      => State
      -> (State -> m (Deeds, Out FVedTerm))
      -> m (Deeds, Out FVedTerm)
split (deeds, Heap h ids, k, (rn, qa)) opt
  = generaliseSplit opt bottom deeds (Heap h ids1, [0..] `zip` k, (case annee qa of Question x -> [rename rn x]; Answer _ -> [], splitQA ids2 (rn, annee qa)))
  where (ids1, ids2) = splitIdSupply ids

{-# INLINE generalise #-}
generalise :: MonadStatics m
           => Generaliser
           -> State
           -> Maybe ((State -> m (Deeds, Out FVedTerm)) -> m (Deeds, Out FVedTerm))
generalise gen (deeds, Heap h ids, k, (rn, qa)) = do
    let named_k = [0..] `zip` k
    
    (gen_kfs, gen_xs') <- case gENERALISATION of
        NoGeneralisation -> Nothing
        AllEligible -> guard (not (IS.null gen_kfs) || not (S.null gen_xs')) >> return (gen_kfs, gen_xs')
          where gen_kfs = IS.fromList [i  | (i, kf) <- named_k, generaliseStackFrame gen kf]
                gen_xs' = S.fromList  [x' | (x', hb) <- M.toList h, generaliseHeapBinding gen x' hb, assertRender ("Bad generalisation", x', hb, heapBindingTag hb) (not (howBound hb == LambdaBound && isNothing (heapBindingTerm hb))) True]
        DependencyOrder want_first -> listToMaybe ((if want_first then id else reverse) possibilities)
          where -- We consider possibilities starting from the root of the term -- i.e. the bottom of the stack.
                -- This is motivated by how the interaction with subgraph generalisation for TreeFlip/TreeSum.
                -- FIXME: explain in more detail if this turns out to be sane.
                possibilities = findGeneralisable False S.empty (reverse named_k) h
                
                findGeneralisable :: Bool -> FreeVars -> NamedStack -> PureHeap -> [(IS.IntSet, S.Set (Out Var))]
                findGeneralisable done_qa pending_xs' unreached_kfs unreached_hbs
                   | done_qa && null pending_kfs && M.null pending_hbs
                   = []
                   | otherwise
                   = [(gen_kf_is, gen_xs') | not (IS.null gen_kf_is) || not (S.null gen_xs')] ++
                     findGeneralisable done_qa' reached_xs' unreached_kfs' unreached_hbs'
                  where
                    (done_qa', extra_pending_xs') = if done_qa || not (null unreached_kfs) then (done_qa, S.empty) else (True, inFreeVars annedFreeVars (rn, qa))
                    (pending_kfs, unreached_kfs') = splitAt 1 unreached_kfs
                    (pending_hbs, unreached_hbs') = M.partitionWithKey (\x' _hb -> x' `S.member` (pending_xs' `S.union` extra_pending_xs')) unreached_hbs
                    
                    gen_kf_is = IS.fromList [i  | (i, kf) <- pending_kfs, generaliseStackFrame gen kf]
                    gen_xs' = S.fromList  [x' | (x', hb) <- M.toList pending_hbs, generaliseHeapBinding gen x' hb, assertRender ("Bad generalisation", x', hb, heapBindingTag hb) (not (howBound hb == LambdaBound && isNothing (heapBindingTerm hb))) True]
                    
                    reached_xs' = M.foldrWithKey (\_x' hb fvs -> heapBindingFreeVars hb `S.union` fvs)
                                                 (S.unions (map (stackFrameFreeVars . tagee . snd) pending_kfs))
                                                 pending_hbs
    
    -- If we can find some fraction of the stack or heap to drop that looks like it will be admissable, just residualise those parts and continue
    traceRender ("gen_kfs", gen_kfs, "gen_xs'", gen_xs') $ return ()
    
    let (ids', ctxt_id) = stepIdSupply ids
    return $ \opt -> generaliseSplit opt (gen_kfs, gen_xs') deeds (Heap h ids', named_k, ([], oneBracketed (Once ctxt_id, \ids -> (0, Heap M.empty ids, [], (rn, fmap qaToAnnedTerm' qa)))))

{-# INLINE generaliseSplit #-}
generaliseSplit :: MonadStatics m
                => (State -> m (Deeds, Out FVedTerm))
                -> (IS.IntSet, S.Set (Out Var))
                -> Deeds
                -> (Heap, NamedStack, ([Out Var], Bracketed (Entered, IdSupply -> UnnormalisedState)))
                -> m (Deeds, Out FVedTerm)
generaliseSplit opt split_from deeds prepared_state = optimiseSplit opt deeds' bracketeds_heap bracketed_focus
  where (deeds', bracketeds_heap, bracketed_focus) = splitt split_from deeds prepared_state

-- Discard dead bindings:
--  let x = ...
--  in 1
-- ==>
--  1
--
-- But include transitively needed ones:
--  let w = ...
--      x = ...
--      y = ... x ...
--      z = ... y ...
--  in z
-- ==>
--  let z = let x = ...
--              y = ... x ...
--          in ... y ...
--  in z
--
-- Inline values and linear things into residual bindings:
--  let x = ... y ...
--      y = ...
--  in \_ -> ... x ...
-- ===>
--  let x = let y = ...
--          in ... y ...
--  in \_ -> ... x ...
--
-- Inline values into residual non-linear things:
--  let x = (y:ys)
--  in \_ -> ... x ...
-- ==>
--  \_ -> let x = (y:ys)
--        in ... x ...
--
-- Do NOT inline linear things into non-linear things:
--  let x = (y:ys)
--      y = ...
--  in \_ -> ... x ...
-- =/=>
-- \_ -> let x = let y = ...
--               in (y:ys)
--       in ... x ...
-- ===>
--  let y = ...
--  in \_ -> let x = (y:ys)
--           in ... x ...
--
-- Inline things that are (apparently) used non-linearly times into linear things:
--  let w = ...
--      x = ... w ...
--      y = ... w ...
--      z = (x, y)
--  in Just z
-- ===>
--  let z = let w = ...
--              x = ... w ...
--              y = ... w ...
--          in (x, y)
--  in Just z
--
-- Treat non-linearity due only to |case| branches as linearity:
--  let x = ...
--  in case unk of C -> ... x ...; D -> ... x ...
-- ===>
--  case unk of C -> let x = ... in ... x ...
--              D -> let x = ... in ... x ...
--
-- Let-float things to trivialise them:
--  let x = let y = ... in (y:xs)
--  in \_ -> ... x ...
-- ===>
--  let y = ....
--  \_ -> let x = (y:xs) in ... x ...
--
-- Note [EC binds something we need to refer to above]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--   let z = f x
--       y = unk + z
--       x = case y of _ -> 2
--   in x + 2
--
-- After splitting:
--   let x = 2
--   in x + 2
-- 
-- That's fine, but how are we going to get a reference to the "x" when residualising the y binding above?
--  let z = f x
--      y = unk + z
--  in case y of _ -> h0
--
-- Lacking extra language features, our only option is to under-specialise the floats by inlining less
-- evaluation context.
data Bracketed a = Bracketed {
    rebuild :: [Out FVedTerm] -> Out FVedTerm, -- Rebuild the full output term given outputs to plug into each hole
    extraFvs :: FreeVars,                      -- Maximum free variables added by the residual wrapped around the holes
    extraBvs :: [BoundVars],                   -- Maximum bound variables added at each hole by the residual wrapped around the holes
    fillers :: [a],                            -- Hole-fillers themselves. Usually State
    tails :: Maybe [Int]                       -- The indexes of all holes in tail position. If this is not Nothing, this is an *exhaustive* list of possible tail positions.
  } deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Accumulatable Bracketed where
    mapAccumTM f acc b = liftM (\(acc', fillers') -> (acc', b { fillers = fillers' })) $ mapAccumTM f acc (fillers b)

noneBracketed :: Out FVedTerm -> FreeVars -> Bracketed a
noneBracketed a b = Bracketed {
    rebuild  = \[] -> a,
    extraFvs = b,
    extraBvs = [],
    fillers  = [],
    tails    = Nothing
  }

oneBracketed :: a -> Bracketed a
oneBracketed x = Bracketed {
    rebuild  = \[e] -> e,
    extraFvs = S.empty,
    extraBvs = [S.empty],
    fillers  = [x],
    tails    = Just [0]
  }

zipBracketeds :: ([Out FVedTerm] -> Out FVedTerm)
              -> ([FreeVars] -> FreeVars)
              -> [BoundVars -> BoundVars]
              -> ([Maybe [Int]] -> Maybe [Int])
              -> [Bracketed a]
              -> Bracketed a
zipBracketeds a b c d bracketeds = Bracketed {
      rebuild  = \(splitManyBy xss -> ess') -> a (zipWith rebuild bracketeds ess'),
      extraFvs = b (map extraFvs bracketeds),
      extraBvs = concat $ zipWith (\c_fn extra_bvs -> map c_fn extra_bvs) c (map extraBvs bracketeds),
      fillers  = concat xss,
      tails    = d $ snd $ foldl (\(i, tailss) bracketed -> (i + length (fillers bracketed), tailss ++ [fmap (map (+ i)) (tails bracketed)])) (0, []) bracketeds
    }
  where xss = map fillers bracketeds

bracketedFreeVars :: (a -> FreeVars) -> Bracketed a -> FreeVars
bracketedFreeVars fvs bracketed = extraFvs bracketed `S.union` transfer (map fvs (fillers bracketed))
  where transfer fvss = S.unions (zipWith (S.\\) fvss (extraBvs bracketed))

releaseBracketedDeeds :: (a -> Deeds) -> Bracketed a -> Deeds
releaseBracketedDeeds release b = sumMap release (fillers b)

modifyFillers :: ([a] -> [b]) -> Bracketed a -> Bracketed b
modifyFillers f bracketed = Bracketed {
    rebuild = rebuild bracketed,
    extraFvs = extraFvs bracketed,
    extraBvs = extraBvs bracketed,
    fillers = f (fillers bracketed),
    tails = tails bracketed
  }

modifyTails :: ([a] -> (b, [a])) -> Bracketed a -> Maybe (b, Bracketed a)
modifyTails f bracketed = do
    is <- tails bracketed
    let (b, fillers') = f (takeIndexes is (fillers bracketed))
    return (b, bracketed { fillers = fillIndexes (is `zip` fillers') (fillers bracketed) })


takeIndexes :: [Int] -> [a] -> [a]
takeIndexes is xs = map (xs !!) is

fillIndexes :: [(Int, a)] -> [a] -> [a]
fillIndexes []             xs = xs
fillIndexes ((i, x'):ixs') xs = fillIndexes ixs' (xs_l ++ x' : xs_r)
  where (xs_l, _:xs_r) = splitAt i xs


optimiseMany :: Monad m
             => ((Deeds, a) -> m (Deeds, Out FVedTerm))
             -> (Deeds, [a])
             -> m (Deeds, [Out FVedTerm])
optimiseMany opt (deeds, xs) = mapAccumLM (curry opt) deeds xs

optimiseBracketed :: MonadStatics m
                  => (State -> m (Deeds, Out FVedTerm))
                  -> (Deeds, Bracketed State)
                  -> m (Deeds, Out FVedTerm)
optimiseBracketed opt (deeds, b) = liftM (second (rebuild b)) $ optimiseMany optimise_one (deeds, extraBvs b `zip` fillers b)
  where optimise_one (deeds, (extra_bvs, (s_deeds, s_heap, s_k, s_e))) = liftM (\(xes, (deeds, e)) -> (deeds, letRecSmart xes e)) $ bindCapturedFloats extra_bvs $ opt (deeds + s_deeds, s_heap, s_k, s_e)
        -- Because h-functions might potentially refer to the lambda/case-alt bound variables around this hole,
        -- we use bindCapturedFloats to residualise such bindings within exactly this context.
        -- See Note [When to bind captured floats]


transformWholeList :: ([a] -> [b]) -- Transformer of concatenated lists -- must be length-preserving!
                   -> [a] -> [[a]] -- Unconcatenated list structures to transform
                   -> ([b], [[b]]) -- Unconcatenated result of transformation
transformWholeList f xs yss = (xs', yss')
  where ys = concat yss
        zs0 = f (xs ++ ys)
        (xs', zs1) = splitBy xs zs0
        (ys', [])  = splitBy ys zs1
        yss' = splitManyBy yss ys'

-- TODO: when driving a residual binding:
--   let x = D[e]
--   in ..
--
-- Arjan Boeijink suggested driving the following instead of D[e]:
--   D[< | e | update x>]
--
-- This can help propagate more positive information, e.g. if e contains an occurrence of x itself
--
-- I'm not doing this right now because I'm wary about the termination issues. We should also be careful that we
-- don't create loops as a result...

optimiseSplit :: MonadStatics m
              => (State -> m (Deeds, Out FVedTerm))
              -> Deeds
              -> M.Map (Out Var) (Bracketed State)
              -> Bracketed State
              -> m (Deeds, Out FVedTerm)
optimiseSplit opt deeds bracketeds_heap bracketed_focus = do
    -- 0) The "process tree" splits at this point. We can choose to distribute the deeds between the children in a number of ways
    let stateSize (_deeds, h, k, in_qa) = heapSize h + stackSize k + qaSize (snd in_qa)
          where qaSize = annedSize . fmap qaToAnnedTerm'
                heapBindingSize hb
                  | InternallyBound <- howBound hb
                  , Just (_, e) <- heapBindingTerm hb
                  = annedSize e
                  | otherwise
                  = 0
                heapSize (Heap h _) = sum (map heapBindingSize (M.elems h))
                stackSize = sum . map (stackFrameSize . tagee)
        bracketSizes = map stateSize . fillers
        
        (heap_xs, bracketeds_heap_elts) = unzip (M.toList bracketeds_heap)
        -- NB: it is *very important* that the list supplied to apportion contains at least one element and at least one non-zero weight, or some
        -- deeds will vanish in a puff of digital smoke. We deal with this in the proportional case by padding the input list with a 1
        (deeds_initial:deeds_focus, deedss_heap)
          | Proportional <- dEEDS_POLICY = transformWholeList (apportion deeds) (1 : bracketSizes bracketed_focus) (map bracketSizes bracketeds_heap_elts)
          | otherwise                    = (deeds : [0 | _ <- bracketSizes bracketed_focus], [[0 | _ <- bracketSizes b] | b <- bracketeds_heap_elts])
        
        bracketeds_deeded_heap = M.fromList (heap_xs `zip` zipWith (\deeds_heap -> modifyFillers (zipWith addStateDeeds deeds_heap)) deedss_heap bracketeds_heap_elts)
        bracketed_deeded_focus = modifyFillers (zipWith addStateDeeds deeds_focus) bracketed_focus
    
    assertRenderM (text "optimiseSplit: deeds lost or gained!", deeds, (deeds_initial, deeds_focus, deedss_heap))
                  (noChange (sumMap (releaseBracketedDeeds releaseStateDeed) bracketeds_heap        + releaseBracketedDeeds releaseStateDeed bracketed_focus        + deeds)
                            (sumMap (releaseBracketedDeeds releaseStateDeed) bracketeds_deeded_heap + releaseBracketedDeeds releaseStateDeed bracketed_deeded_focus + deeds_initial))
    
    -- 1) Recursively drive the focus itself
    let extra_statics = M.keysSet bracketeds_heap
    (hes, (leftover_deeds, e_focus)) <- bindCapturedFloats extra_statics $ optimiseBracketed opt (deeds_initial, bracketed_deeded_focus)
    
    -- 2) We now need to think about how we are going to residualise the letrec. In fact, we need to loop adding
    -- stuff to the letrec because it might be the case that:
    --  * One of the hes from above refers to some heap binding that is not referred to by the let body
    --  * So after we do withStatics above we need to drive some element of the bracketeds_heap
    --  * And after driving that we find in our new hes a new h function referring to a new free variable
    --    that refers to some binding that is as yet unbound...
    (leftover_deeds, bracketeds_deeded_heap, xes, _fvs) <- go hes extra_statics leftover_deeds bracketeds_deeded_heap [] (fvedTermFreeVars e_focus)
    
    -- 3) Combine the residualised let bindings with the let body
    return (sumMap (releaseBracketedDeeds releaseStateDeed) bracketeds_deeded_heap + leftover_deeds,
            letRecSmart xes e_focus)
  where
    -- TODO: clean up this incomprehensible loop
    -- TODO: investigate the possibility of just fusing in the optimiseLetBinds loop with this one
    go hes extra_statics leftover_deeds bracketeds_deeded_heap xes fvs = do
        let extra_statics' = extra_statics `S.union` S.fromList (map fst hes) -- NB: the statics already include all the binders from bracketeds_deeded_heap, so no need to add xes stuff
        (hes', (leftover_deeds, bracketeds_deeded_heap, fvs, xes')) <- bindCapturedFloats extra_statics' $ optimiseLetBinds opt leftover_deeds bracketeds_deeded_heap (fvs `S.union` S.unions (map (fvedTermFreeVars . snd) hes)) -- TODO: no need to get FVs in this way (they are in Promise)
        (if null hes' then (\a b c d -> return (a,b,c,d)) else go hes' extra_statics') leftover_deeds bracketeds_deeded_heap (xes ++ [(x', e') | (x', e') <- hes, x' `S.member` fvs] ++ xes') fvs


-- We only want to drive (and residualise) as much as we actually refer to. This loop does this: it starts
-- by residualising the free variables of the focus residualisation (or whatever is in the let body),
-- and then transitively inlines any bindings whose corresponding binders become free.
optimiseLetBinds :: MonadStatics m
                 => (State -> m (Deeds, Out FVedTerm))
                 -> Deeds
                 -> M.Map (Out Var) (Bracketed State)
                 -> FreeVars
                 -> m (Deeds, M.Map (Out Var) (Bracketed State), FreeVars, Out [(Var, FVedTerm)])
optimiseLetBinds opt leftover_deeds bracketeds_heap fvs' = -- traceRender ("optimiseLetBinds", M.keysSet bracketeds_heap, fvs') $
                                                           go leftover_deeds bracketeds_heap [] fvs'
  where
    go leftover_deeds bracketeds_deeded_heap_not_resid xes_resid resid_fvs
      | M.null h_resid = return (leftover_deeds, bracketeds_deeded_heap_not_resid, resid_fvs, xes_resid)
      | otherwise = {- traceRender ("optimiseSplit", xs_resid') $ -} do
        -- Recursively drive the new residuals arising from the need to bind the resid_fvs
        (leftover_deeds, es_resid') <- optimiseMany (optimiseBracketed opt) (leftover_deeds, bracks_resid)
        let extra_resid_fvs' = S.unions (map fvedTermFreeVars es_resid')
        -- Recurse, because we might now need to residualise and drive even more stuff (as we have added some more FVs and BVs)
        go leftover_deeds bracketeds_deeded_heap_not_resid'
                          (xes_resid ++ zip xs_resid' es_resid')
                          (resid_fvs `S.union` extra_resid_fvs')
      where
        -- When assembling the final list of things to drive, ensure that we exclude already-driven things
        (h_resid, bracketeds_deeded_heap_not_resid') = M.partitionWithKey (\x _br -> x `S.member` resid_fvs) bracketeds_deeded_heap_not_resid
        (xs_resid', bracks_resid) = unzip $ M.toList h_resid

type NamedStack = [(Int, Tagged StackFrame)]

splitt :: (IS.IntSet, S.Set (Out Var))
       -> Deeds
       -> (Heap, NamedStack, ([Out Var], Bracketed (Entered, IdSupply -> UnnormalisedState)))         -- ^ The thing to split, and the Deeds we have available to do it
       -> (Deeds,                             -- ^ The Deeds still available after splitting
           M.Map (Out Var) (Bracketed State), -- ^ The residual "let" bindings
           Bracketed State)                   -- ^ The residual "let" body
splitt (gen_kfs, gen_xs) old_deeds (cheapifyHeap old_deeds -> (deeds, Heap h (splitIdSupply -> (ids_brack, ids))), named_k, (scruts, bracketed_qa))
    = snd $ split_step split_fp
      -- Once we have the correct fixed point, go back and grab the associated information computed in the process
      -- of obtaining the fixed point. That is what we are interested in, not the fixed point itselF!
      -- TODO: eliminate redundant recomputation here?
  where
    -- We compute the correct way to split as a least fixed point, slowly building up a set of variables
    -- (bound by heap bindings and update frames) that it is safe *not* to residualise.
    --
    -- Note that as an optimisation, optimiseSplit will only actually creates those residual bindings if the
    -- corresponding variables are free *after driving*. Of course, we have no way of knowing which bindings
    -- will get this treatment here, so just treat resid_xs as being exactly the set of residualised stuff.
    split_fp = lfpFrom (S.empty, S.empty) (fst . split_step)
    
    -- Simultaneously computes the next fixed-point step and some artifacts computed along the way,
    -- which happen to correspond to exactly what I need to return from splitt.
    split_step (safe_not_resid_xs, deeds_resid_xs) = -- let pPrintBracketedState = map pPrintFullState . fillers in traceRender ("split_step", (not_resid_xs, bound_xs S.\\ not_resid_xs), pureHeapBoundVars h_not_residualised, pureHeapBoundVars h_residualised, M.map pPrintBracketedState bracketeds_heap', pPrintBracketedState bracketed_focus') $
                                                     ((safe_not_resid_xs', deeds_resid_xs'), (deeds4, bracketeds_heap', bracketed_focus'))
      where
        -- 0) Compute the set of variables that I can *actually* get away without residualising, once deeds are accounted for
        -- See Note [Deeds and splitting] for further details on this.
        not_resid_xs = safe_not_resid_xs S.\\ deeds_resid_xs
        
        -- 1) Build a candidate splitting for the Stack and QA components
        -- When creating the candidate stack split, we ensure that we create a residual binding
        -- for any variable in the resid_xs set, as we're not going to inline it to continue.
        --
        -- We also take this opportunity to fill in the IdSupply required by each prospective new State.
        -- We can use the same one for each context because there is no danger of shadowing.
        fill_ids :: Bracketed (Entered, IdSupply -> UnnormalisedState) -> Bracketed (Entered, UnnormalisedState) -- NB: do NOT normalise at this stage because in transitiveInline we assume that State heaps are droppable!
        fill_ids = fmap (\(ent, f) -> (ent, f ids_brack))
        (deeds1, bracketeds_updated, bracketed_focus)
          = (\(a, b, c) -> (a, M.map fill_ids b, fill_ids c)) $
            pushStack ids deeds scruts [(need_not_resid_kf i kf, kf) | (i, kf) <- named_k] bracketed_qa
            
        need_not_resid_kf i kf
          | i `IS.member` gen_kfs
          = False
          | Update x' <- tagee kf -- We infer the stack frames we're not residualising based on the *variables* we're not residualising
          = x' `S.member` not_resid_xs
          | otherwise
          = True
        
        -- 2) Build a splitting for those elements of the heap we propose to residualise not in not_resid_xs
        -- TODO: I should residualise those Unfoldings whose free variables have become interesting due to intervening scrutinisation
        (h_not_residualised, h_residualised) = M.partitionWithKey (\x' _ -> x' `S.member` not_resid_xs) h
        bracketeds_nonupdated = M.mapMaybeWithKey (\x' hb -> do { guard (howBound hb == InternallyBound); in_e <- heapBindingTerm hb; return (fill_ids $ oneBracketed (Once (fromJust (name_id x')), \ids -> (0, Heap M.empty ids, [], in_e))) }) h_residualised
        -- For every heap binding we ever need to deal with, contains a version of that heap binding as a concrete Bracketed thing
        bracketeds_heap = bracketeds_updated `M.union` bracketeds_nonupdated
        
        -- 3) Inline as much of the Heap as possible into the candidate splitting
        
        -- 3a) Release deeds
        -- In order to make the Deeds-based stuff less conservative, my first action here is to release our claims to those deeds
        -- which we do *not* intend to create a residual let binding for here and now. This will let us always inline a heap-bound
        -- thing into *at least one* context (unless it really is referred to by the residual code).
        --
        -- The equivalent process is done for the stack in splitStack itself: we just subtract 1 from the number of deeds we need to
        -- claim when duplicating a stack frame.
        deeds2 = releasePureHeapDeeds deeds1 h_not_residualised
        
        -- 3b) Work out which part of the heap is admissable for inlining
        -- * We are allowed to inline concrete things which are duplicatable or are not residualised right here and now
        -- * Non-concrete stuff should be inlined if and only if it is not explicitly residualised by the caller. The motivation that
        --   if we generalise away a term, we want to generalise away the staticness as well. Furthermore, it is clear that if we are
        --   just generalising away staticness itself we certainly should not push the corresponding non-concrete binding down.
        -- * We take this opportunity to mark all residualised things as static (being careful to not override actual definitions in h_cheap).
        --   It important that we do not mark residualised things as phantoms just because they are in bracketeds_heap. If we did, it would mean
        --   that *concrete residualised stuff* is recorded as a phantom even if it was explicitly residualised in the initial iteration (since
        --   anything residualised in the first iteration is certainly in bracketeds_heap).
        -- * If we are inlining a value (into a non-linear context), we are careful to only inline an *indirection* to that value. That
        --   allows us to prevent duplicating the allocation of such values. NB: we still duplicate allocation of cheap non-values, but never mind...
        --
        -- Inlineable things are either:
        --  1) Heap bindings from the input (i.e from the heap and update frames) that have not been residualised for work duplication reasons
        --  2) Concrete values and cheap expressions from the input, in a form that is suitable for pushing down (i.e. values have been turned into indirections).
        --  3) Phantom versions of phantom input heap bindings (just copied verbatim).
        --  4) Phantom versions of concrete input heap bindings
        -- The range of this heap is lte that of bracketeds_heap. We explicitly EXCLUDE those bindings that we are residualising based on the generalisation heuristic.
        -- We prefer input heap bindings to everything else, and concrete values/cheap expressions to phantoms. For example, even if a value is residualised, we would
        -- like to push down *some* version of it, hence the h_cheap full of indirections. And even if a concrete term is residualised we'd like a phantom version of it.
        --
        -- Basically the idea of this heap is "stuff we want to make available to push down"
        h_updated_phantoms = M.fromDistinctAscList [(x', lambdaBound) | x' <- M.keys bracketeds_updated] -- TODO: move this into h_cheap_and_phantoms?
        h_inlineable = setToMap lambdaBound gen_xs `M.union` -- The exclusion just makes sure we don't inline explicitly generalised bindings (even phantom ones)
                       (h_not_residualised `M.union`         -- Take any non-residualised bindings from the input heap/stack...
                        h_cheap_and_phantom `M.union`        -- ...failing which, take concrete definitions for cheap heap bindings (even if they are also residualised) or phantom definitions for expensive ones...
                        h_updated_phantoms)                  -- ...failing which, take phantoms for things bound by update frames (if supercompilation couldn't turn these into values, GHC is unlikely to get anything good from seeing defs)
        
        -- Generalising the final proposed floats may cause some bindings that we *thought* were going to be inlined to instead be
        -- residualised. We need to account for this in the Entered information (for work-duplication purposes), and in that we will
        -- also require any FVs of the new residualised things that are bound in the stack to residualise more frames.
        inlineHeapT :: Accumulatable t
                    => (Deeds -> a   -> (Deeds, EnteredEnv, b))
                    ->  Deeds -> t a -> (Deeds, EnteredEnv, t b)
        inlineHeapT f deeds b = (deeds', entered', b')
          where ((deeds', entered'), b') = mapAccumT (\(deeds, entered) s -> case f deeds s of (deeds, entered', s) -> ((deeds, entered `join` entered'), s)) (deeds, bottom) b

        -- Inline what we can of the heap, and compute the Entered information for the resulting thing.
        -- See Note [transitiveInline and entered information] for the story about Entered information.
        --
        -- TODO: I (probably) need to transfer the EnteredEnv safely out of Bracketed things, taking account of bound variables
        -- over the holes. However, I think it's probably safe to ignore that for now because those bound variables will have been
        -- renamed so as not to coincide with any of the heap/stack bindings above that we actually care about the entered information for.
        -- So the outgoing entered envs will have a bit of junk in them, but who cares?
        inlineBracketHeap :: Deeds -> Bracketed (Entered, UnnormalisedState) -> (Deeds, EnteredEnv, Bracketed State)
        inlineBracketHeap = inlineHeapT inline_one
          where
            inline_one deeds (ent, state) = (deeds', mkEnteredEnv ent $ stateFreeVars state', (0, heap', k', in_e'))
              where
                -- The elements of the Bracketed may contain proposed heap bindings gathered from Case frames.
                -- However, we haven't yet claimed deeds for them :-(.
                --
                -- This is OK, because transitiveInline treats the heap of its state "specially". NB: the correctness
                -- of this relies on the fact that only "optional" bindings that shadow something bound above are ever
                -- present in this heap.
                --
                -- We do the normalisation immediately afterwards - we can't do it before transitiveInline, precisely
                -- because of the above hack (normalisation might add bindings to the heap).
                state'@(deeds', heap', k', in_e') = normalise $ transitiveInline h_inlineable (deeds `addStateDeeds` state)
        
        -- 3c) Actually do the inlining of as much of the heap as possible into the proposed floats
        -- We also take this opportunity to strip out the Entered information from each context.
        (deeds3, entered_focus, bracketed_focus') =             inlineBracketHeap deeds2 bracketed_focus
        (deeds4, entered_heap,  bracketeds_heap') = inlineHeapT inlineBracketHeap deeds3 bracketeds_heap

        -- 4) Construct the next element of the fixed point process:
        --  a) We should residualise:
        --     * Any x in the extraFvs of a bracketed thing, because we need to be able to refer to it right here, whatever happens
        --     * Anything explicitly generalised
        must_resid_xs = extraFvs bracketed_focus' `S.union` S.unions (map extraFvs (M.elems bracketeds_heap'))
                          `S.union` gen_xs
        --  b) We should *stop* residualising bindings that got Entered only once in the proposal.
        --     I once thought that we should only add a single variable to non_resid_xs' every time around the loop, because I worried
        --     that choosing not to residualise some binding would cause some other bindings to stop being candiates (i.e. would increase
        --     the number of times they were entered).
        --
        --     However, I've revised my opinion and decided to add all candidate variables every time. This is because if we inline a binding
        --     into a context where it is still evaluated Once, anything it refers to is still evaluated Once. So the existing Entered information
        --     does not appear to be invalidated when we decide not to residualise an additional binding.
        entered    = entered_focus `join` entered_heap
        safe_not_resid_xs' = -- traceRender ("candidates", onces, must_resid_xs, not_resid_xs, candidates S.\\ not_resid_xs) $
                             safe_not_resid_xs `S.union` (onces S.\\ must_resid_xs)
          where onces = S.filter (\x' -> maybe True isOnce (M.lookup x' entered)) bound_xs
        --   c) We should *start* residualising those bindings we thought were safe to inline but we actually couldn't inline because
        --      deeds issues prevented us from inlining them into *all* contexts that needed them. See also Note [Deeds and splitting]
        --
        --      This should also deal with residualising any InternallyBound stuff that we decided to instead let/lambda bound to e.g. prevent
        --      value duplication, because the names of such bound things will be free in the proposed states.
        deeds_resid_xs' = deeds_resid_xs `S.union` (safe_not_resid_xs `S.intersection` (bracketedFreeVars stateFreeVars bracketed_focus' `S.union`
                                                                                        S.unions (map (bracketedFreeVars stateFreeVars) (M.elems bracketeds_heap'))))
    
    -- Bound variables: those variables that I am interested in making a decision about whether to residualise or not
    bound_xs = pureHeapBoundVars h `S.union` stackBoundVars (map snd named_k)
    
    -- Heap full of cheap expressions and any phantom stuff from the input heap but NOT from update frames
    -- Used within the main loop in the process of computing h_inlineable -- see comments there for the full meaning of this stuff.
    extract_cheap_hb hb
       -- We better not try to push down any bindings that would introduce work-duplication issues
      | InternallyBound <- howBound hb
      , Just (_, e) <- heapBindingTerm hb
      = if isCheap (annee e)
        then hb {                            howBound = howToBindCheap e } -- Use binding heuristics to determine how to refer to the cheap thing
        else hb { heapBindingTerm = Nothing, howBound = LambdaBound }      -- GHC is unlikely to get any benefit from seeing the binding sites for non-cheap things
       -- Inline phantom/unfolding stuff verbatim: there is no work duplication issue (the caller would not have created the bindings unless they were safe-for-duplication)
      | otherwise
      = hb
    h_cheap_and_phantom = M.map extract_cheap_hb h

howToBindCheap :: AnnedTerm -> HowBound
howToBindCheap e
  | not lOCAL_TIEBACKS = InternallyBound
  | dUPLICATE_VALUES_SPLITTER = InternallyBound
  | Value v <- annee e = case v of
    Lambda _ _ -> LetBound -- Heuristic: GHC would lose too much if we cut the connection between the definition and use sites
    Data _ xs | null xs   -> InternallyBound -- Heuristic: GHC will actually statically allocate data with no arguments (this also has the side effect of preventing tons of type errors due to [] getting shared)
              | otherwise -> LambdaBound
    Literal _  -> InternallyBound -- No allocation duplication since GHC will float them (and common them up, if necessary)
    Indirect _ -> InternallyBound -- Always eliminated by GHC
   -- GHC is unlikely to get anything useful from seeing the definition of cheap non-values, so we'll have them as unfoldings
  | otherwise = LambdaBound

-- Note [Deeds and splitting]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Some heap bindings are safe to inline (from a work-duplication perspective), but bad to inline from a deeds perspective
-- because it can prove impossible to get enough deeds to actually inline them. We apply a rather unsubtle (but safe)
-- heuristic to deal with this situation, by monotonically growing a set of variables that we should *not* attempt
-- to inline even though they appear in the safe_not_resid_xs set.
-- 
-- This really is extremely conservative, but if we're running out of deeds bad things will happen anyway, so who cares?
--
-- If we did not do this, then the bracketed_heap outgoing from splitt may not bind some of the variables free in what
-- it intends to drive, because bracketeds_heap only contains those bindings that splitt decided should be residualised.


-- Note [Residualisation of things referred to in extraFvs]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- We need to residualise stuff like the a and b in this:
--  <a |-> 1, b |-> 2 | (a, b) | >
--
-- But *not* the x in this:
--  < | foo | case foo of \Delta, update x, [_] + 1 >
--
-- How the hell do we accomplish that? The trick is to change how update frames get split. After splitting an
-- update frame for x, I continue splitting the rest of the stack with a oneBracketed rather than a noneBracketed in
-- the focus.
--
-- If I didn't do this, the extraFvs of the bracket would indicate that x was free in a created residual term, so I
-- would be forced to residualise the binding just as if e.g. "Just x" had been in the focus of the state. Since I don't,
-- x doesn't appear in the extraFvs, and I can compute Entered information for it with transitiveInline. If this says x
-- was entered Once in aggregate I can stop residualising the update frame! Beautiful!
--
-- Note [Entered information]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Consider:
--   expensive |-> fact 100
--   a |-> Just expensive
--   b |-> Just expensive
--   (a, b)
--
-- We need to residualise expensive, but what is the mechanism for doing so? Both a and b will get residualised
-- by the rule above because they are FVs of the focus.
--
-- We gather Entered information from each proposed Bracketed to collect Entered information for each free variable.
-- This reports how many times a variable would be (in the worst case) get reevaluated if the binding was made available
-- for inlining and thus pushed into that context. So in this case, Entered information for the a and b bindings report
-- that expensive would get evaluated Once in each context, which joins together to make Many times.
--
-- This is the basis on which we choose to residualise expensive.

-- We are going to use this helper function to inline any eligible inlinings to produce the expressions for driving.
--
-- WARNING! We treat bindings in the incoming Heap very specially we assume that we haven't yet claimed any deeds for them
--
-- This is a consequence of the fact that this heap is only non-empty in the splitter for states originating from the
-- branch of some residual case expression.
transitiveInline :: PureHeap          -- ^ What to inline. We have not claimed deeds for any of this.
                 -> UnnormalisedState -- ^ What to inline into
                 -> UnnormalisedState
transitiveInline init_h_inlineable _state@(deeds, Heap h ids, k, in_e)
    = -- (if not (S.null not_inlined_vs') then traceRender ("transitiveInline: generalise", not_inlined_vs') else id) $
      -- traceRender ("transitiveInline", "had bindings for", pureHeapBoundVars init_h_inlineable, "FVs were", state_fvs, "so inlining", pureHeapBoundVars h') $
      assertRender ("transitiveInline", M.keysSet h_inlineable, pPrintFullUnnormalisedState _state, pPrintFullUnnormalisedState state', stateUncoveredVars state', M.keysSet h', live') (S.null (stateUncoveredVars state'))
      state'
  where
    state' = (deeds', Heap h' ids, k, in_e)
    
    (live', deeds', h') = heap_worker 0 deeds M.empty (stateFreeVars (deeds, Heap M.empty ids, k, in_e)) S.empty
    
    -- NB: we prefer bindings from h to those from init_h_inlineable if there is any conflict. This is motivated by
    -- the fact that bindings from case branches are usually more informative than e.g. a phantom binding for the scrutinee.
    h_inlineable = h `M.union` init_h_inlineable
    
    -- This function is rather performance critical: I originally benchmarked transitiveInline as taking 59.2% of runtime for DigitsOfE2!
    heap_worker :: Int -> Deeds -> PureHeap -> FreeVars -> FreeVars -> (FreeVars, Deeds, PureHeap)
    heap_worker n deeds h_output live live_in_let
      = -- traceRender ("go", n, M.keysSet h_inlineable, M.keysSet h_output, fvs) $
        if live == live'
        then (live', deeds', neutraliseLetLives live_in_let' h_output') -- NB: it's important we use the NEW versions of h_output/deeds, because we might have inlined extra stuff even though live hasn't changed!
        else heap_worker (n + 1) deeds' h_output' live' live_in_let'
      where 
        (deeds', h_output', live', live_in_let') = M.foldrWithKey consider_inlining (deeds, h_output, live, live_in_let) ((h_inlineable `restrict` live) M.\\ h_output)
        
        -- NB: we rely here on the fact that our caller will still be able to fill in bindings for stuff from h_inlineable
        -- even if we choose not to inline it into the State, and that such bindings will not be evaluated until they are
        -- actually demanded (or we could get work duplication by inlining into only *some* Once contexts).
        --
        -- NB: we also rely here on the fact that the original h contains "optional" bindings in the sense that they are shadowed
        -- by something bound above - i.e. it just tells us how to unfold case scrutinees within a case branch.
        consider_inlining x' hb (deeds, h_output, live, live_in_let)
          = (deeds', M.insert x' inline_hb h_output, live `S.union` fvs, if howBound inline_hb == LetBound then live_in_let `S.union` fvs else live_in_let)
          where fvs = heapBindingFreeVars inline_hb
                (deeds', inline_hb) = case claimDeeds deeds (heapBindingSize hb) of -- Do we have enough deeds to inline an unmodified version?
                  Just deeds' ->                                                     (deeds', hb)
                  Nothing     -> trace (render $ text "inline-deeds:" <+> pPrint x') (deeds,  makeFreeForDeeds hb)

    -- Given a HeapBinding that costs some deeds, return one that costs no deeds (and so can be inlined unconditionally)
    makeFreeForDeeds (HB InternallyBound (Just in_e))
      | not lOCAL_TIEBACKS     = lambdaBound        -- Without local tiebacks, we just lose information here
      | termIsCheap (snd in_e) = HB how (Just in_e) -- With local tiebacks, we can keep the RHS (perhaps we can use it in the future?) but have to make it be able to pass it in from the caller somehow
      | otherwise              = lambdaBound        -- All non-cheap things
      where how | termIsValue (snd in_e) = LetBound    -- Heuristic: only refer to *values* via a free variable, as those are the ones GHC will get some benefit from. TODO: make data/function distinction here?
                | otherwise              = LambdaBound
    makeFreeForDeeds hb = panic "howToBind: should only be needed for internally bound things with a term" (pPrint hb)
    
    -- Enforce the invariant that anything referred to by a LetBound thing cannot be LambdaBound
    neutraliseLetLives live_in_let = M.mapWithKey (\x' hb -> if howBound hb == LambdaBound && x' `S.member` live_in_let then hb { howBound = LetBound } else hb)

-- TODO: replace with a genuine evaluator. However, think VERY hard about the termination implications of this!
-- I think we can only do it when the splitter is being invoked by a non-whistling invocation of sc.
cheapifyHeap :: Deeds -> Heap -> (Deeds, Heap)
cheapifyHeap deeds heap | not sPLITTER_CHEAPIFICATION = (deeds, heap)
cheapifyHeap deeds (Heap h (splitIdSupply -> (ids, ids'))) = (deeds', Heap (M.fromList [(x', internallyBound in_e) | (x', in_e) <- floats] `M.union` h') ids')
  where
    ((deeds', _, floats), h') = M.mapAccum (\(deeds, ids, floats0) hb -> case hb of HB InternallyBound (Just in_e) -> (case cheapify deeds ids in_e of (deeds, ids, floats1, in_e') -> ((deeds, ids, floats0 ++ floats1), HB InternallyBound (Just in_e'))); _ -> ((deeds, ids, floats0), hb)) (deeds, ids, []) h
    
    -- TODO: make cheapification more powerful (i.e. deal with case bindings)
    cheapify :: Deeds -> IdSupply -> In AnnedTerm -> (Deeds, IdSupply, [(Out Var, In AnnedTerm)], In AnnedTerm)
    cheapify deeds0 ids0 (rn, (annee -> LetRec xes e)) = (deeds3, ids3, zip in_xs in_es' ++ floats0 ++ floats1, in_e')
      where deeds1 = deeds0 + 1
            (        ids1, rn', unzip -> (in_xs, in_es)) = renameBounds (\_ x' -> x') ids0 rn xes
            (deeds2, ids2, floats0, in_es') = cheapifyMany deeds1 ids1 in_es
            (deeds3, ids3, floats1, in_e')  = cheapify deeds2 ids2 (rn', e)
    cheapify deeds ids in_e = (deeds, ids, [], in_e)

    cheapifyMany :: Deeds -> IdSupply -> [In AnnedTerm] -> (Deeds, IdSupply, [(Out Var, In AnnedTerm)], [In AnnedTerm])
    cheapifyMany deeds ids = reassociate . mapAccumL ((associate .) . uncurry cheapify) (deeds, ids)
      where reassociate ((deeds, ids), unzip -> (floatss, in_es)) = (deeds, ids, concat floatss, in_es)
            associate (deeds, ids, floats, in_e) = ((deeds, ids), (floats, in_e))


-- TODO: I have a clever idea. Currently, if we supercompile:
--  D[ < H | if x then y else z | K > ]
--
-- And we don't know anything about y or z we get:
--  if x
--   then K(True/x)[y]
--   else K(False/x)[z]
--
-- This is not too bad, but I suspect that it is common that K doesn't actually depend on x, in which case we could
-- instead produce:
--  let $j it = K[it]
--  in if x then $j y else $j z
--
-- This is an improvement because we get code sharing. Furthermore, $j won't be causing extra allocation because it's
-- pretty much guaranteed to be a let-no-escape.
--
-- The best part is that making this happen isn't really much much work (I think). One option would be to actually add
-- a (JoinPoint Var) stack frame, and introduce them (along with their corresponding bindings) in the splitter. The reduction
-- rule would be:
--   < H | v | $j [_], K > --> < H, x |-> v | e | K >
--      \x.e = deref(H, $j)
--
-- If we said join points were LetBound this would also let us delay inlining them (and hence consuming deeds) until we
-- were sure we could get some benefit from it.
--
-- The major issue is exactly what *should* be bound up into a join point. We could create one per stack frame, but that
-- might lead to quite a lot of code bloat. I think that ideally we want to create one per shared stack suffix: there is no
-- point creating join points that are only used in one place! But how to detect that?? After all, because h-functions can
-- be tied back to at any later point it looks like we should create one for every possible prefix as they might be useful
-- for guys in the future.
pushStack :: IdSupply
          -> Deeds
          -> [Out Var]
          -> [(Bool, Tagged StackFrame)]
          -> Bracketed (Entered, IdSupply -> UnnormalisedState)
          -> (Deeds,
              M.Map (Out Var) (Bracketed (Entered, IdSupply -> UnnormalisedState)),
              Bracketed (Entered, IdSupply -> UnnormalisedState))
pushStack _   deeds _      []                 bracketed_hole = (deeds, M.empty, bracketed_hole)
pushStack ids deeds scruts ((may_push, kf):k) bracketed_hole = second3 (`M.union` bracketed_heap') $ pushStack ids2 deeds' scruts' k bracketed_hole'
  where
    (ids1, ids2) = splitIdSupply ids

    -- If we have access to hole tail positions, we should try to inline this stack frame into that tail position.
    -- If we do not have access to the tail positions of the hole, all we can do is rebuild a bit of residual syntax around the hole.
    (deeds', (scruts', bracketed_heap', bracketed_hole'))
      = (guard may_push >> fmap (\(deeds', bracketed_hole') -> (deeds', ([], M.empty, bracketed_hole'))) (pushStackFrame kf deeds bracketed_hole)) `orElse`
        (deeds, splitStackFrame ids1 kf scruts bracketed_hole)

pushStackFrame :: Tagged StackFrame
               -> Deeds
               -> Bracketed (Entered, IdSupply -> UnnormalisedState)
               -> Maybe (Deeds, Bracketed (Entered, IdSupply -> UnnormalisedState))
pushStackFrame kf deeds bracketed_hole = do
    (Just deeds', bracketed_hole') <- modifyTails push bracketed_hole
    return (deeds', bracketed_hole')
  where
    -- Inline parts of the evaluation context into each branch only if we can get that many deeds for duplication
    push fillers = case claimDeeds deeds (stackFrameSize (tagee kf) * (branch_factor - 1)) of -- NB: subtract one because one occurrence is already "paid for". It is OK if the result is negative (i.e. branch_factor 0)!
            Nothing    -> trace (render $ text "pushStack-deeds" <+> pPrint branch_factor) (Nothing, fillers)
            Just deeds ->                                                                  (Just deeds, map (\(ent, f) -> (ent, third4 (++ [kf]) . f)) fillers)
      where branch_factor = length fillers

splitStackFrame :: IdSupply
                -> Tagged StackFrame
                -> [Out Var]
                -> Bracketed (Entered, IdSupply -> UnnormalisedState)
                -> ([Out Var],
                    M.Map (Out Var) (Bracketed (Entered, IdSupply -> UnnormalisedState)),
                    Bracketed (Entered, IdSupply -> UnnormalisedState))
splitStackFrame ids kf scruts bracketed_hole
  | Update x' <- tagee kf = splitUpdate (tag kf) scruts x' bracketed_hole
  | otherwise = ([], M.empty, case tagee kf of
    Apply x2' -> zipBracketeds (\[e] -> e `app` x2') (\[fvs] -> S.insert x2' fvs) [id] (\_ -> Nothing) [bracketed_hole]
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    -- (if not (null k_not_inlined) then traceRender ("splitStack: generalise", k_not_inlined) else id) $
                                                    zipBracketeds (\(e_hole:es_alts) -> case_ e_hole (alt_cons' `zip` es_alts)) (\(fvs_hole:fvs_alts) -> fvs_hole `S.union` S.unions (zipWith (S.\\) fvs_alts alt_bvss)) (id:[\bvs -> bvs `S.union` alt_bvs | alt_bvs <- alt_bvss]) (\(_tails_hole:tailss_alts) -> liftM concat (sequence tailss_alts)) (bracketed_hole : bracketed_alts)
      where -- 0) Manufacture context identifier
            (ids', state_ids) = splitIdSupply ids
            ctxt_id = idFromSupply state_ids
            
            -- 1) Construct the floats for each case alternative
            (_alt_ids', alt_rns, alt_cons') = unzip3 $ map (renameAltCon ids' rn) alt_cons
            -- Bind something to the case scrutinee (if possible). This means that:
            --  let y = (\z -> case z of C -> ...) unk
            --  in y
            -- ===>
            --  case x of C -> let unk = C; z = C in ...
            alt_in_es = alt_rns `zip` alt_es
            alt_hs = zipWith4 (\alt_rn alt_con alt_bvs alt_tg -> setToMap lambdaBound alt_bvs `M.union` M.fromList (do { Just scrut_v <- [altConToValue alt_con]; scrut_e <- [annedTerm alt_tg (Value scrut_v)]; scrut <- scruts; return (scrut, HB (howToBindCheap scrut_e) (Just (alt_rn, scrut_e))) })) alt_rns alt_cons alt_bvss (map annedTag alt_es) -- NB: don't need to grab deeds for these just yet, due to the funny contract for transitiveInline
            alt_bvss = map (\alt_con' -> fst $ altConOpenFreeVars alt_con' (S.empty, S.empty)) alt_cons'
            bracketed_alts = zipWith (\alt_h alt_in_e -> oneBracketed (Once ctxt_id, \ids -> (0, Heap alt_h ids, [], alt_in_e))) alt_hs alt_in_es
    PrimApply pop in_vs in_es -> zipBracketeds (primOp pop) S.unions (repeat id) (\_ -> Nothing) (bracketed_vs ++ bracketed_hole : bracketed_es)
      where -- 0) Manufacture context identifier
            (ids', state_idss) = accumL splitIdSupply ids (length in_es)
            ctxt_ids = map idFromSupply state_idss
            
            -- 1) Split every value and expression remaining apart
            bracketed_vs = map (splitValue ids' . fmap annee) in_vs
            bracketed_es  = zipWith (\ctxt_id in_e -> oneBracketed (Once ctxt_id, \ids -> (0, Heap M.empty ids, [], in_e))) ctxt_ids in_es)
  where
    altConToValue :: AltCon -> Maybe (ValueF ann)
    altConToValue (DataAlt dc xs) = Just $ Data dc xs
    altConToValue (LiteralAlt l)  = Just $ Literal l
    altConToValue (DefaultAlt _)  = Nothing

-- I'm making use of a clever trick: after splitting an update frame for x, instead of continuing to split the stack with a
-- noneBracketed for x in the focus, I split the stack with a oneBracketed for it in the focus.
--
-- You might think this is utterly worthless, since by definition the splitter will never be able to push the actual definition of
-- x into this hole in the bracketed. However, the fact that we do this is *critical* to the algorithm I use to ensure that
-- we can make variables bound by update frames as non-residualised: see Note [Residualisation of things referred to in extraFvs]
splitUpdate :: Tag -> [Out Var] -> Var -> Bracketed (Entered, IdSupply -> UnnormalisedState)
            -> ([Out Var], M.Map (Out Var) (Bracketed (Entered, IdSupply -> UnnormalisedState)), Bracketed (Entered, IdSupply -> UnnormalisedState))
splitUpdate tg_kf scruts x' bracketed_hole = (x' : scruts, M.singleton x' bracketed_hole,
                                              oneBracketed (Once ctxt_id, \ids -> (0, Heap M.empty ids, [], (mkIdentityRenaming [x'], annedTerm tg_kf (Var x')))))
  where
    ctxt_id = fromJust (name_id x')

splitValue :: IdSupply -> In AnnedValue -> Bracketed (Entered, IdSupply -> UnnormalisedState)
splitValue ids (rn, Lambda x e) = zipBracketeds (\[e'] -> lambda x' e') (\[fvs'] -> fvs') [S.insert x'] (\_ -> Nothing) [oneBracketed (Many, \ids -> (0, Heap (M.singleton x' lambdaBound) ids, [], (rn', e)))]
  where (_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v             = noneBracketed (value v') (inFreeVars annedValueFreeVars' in_v)
  where v' = detagAnnedValue' $ renameIn (renameAnnedValue' ids) in_v

splitQA :: IdSupply -> In QA -> Bracketed (Entered, IdSupply -> UnnormalisedState)
splitQA _   (rn, Question x) = noneBracketed (var x') (S.singleton x')
  where x' = rename rn x
splitQA ids (rn, Answer v)   = splitValue ids (rn, v)
