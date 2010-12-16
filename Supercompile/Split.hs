{-# LANGUAGE PatternGuards, ViewPatterns, TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable,
             MultiParamTypeClasses, FlexibleInstances, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (MonadStatics(..), split, transitiveInline) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate
import Evaluator.FreeVars
--import Evaluator.Residualise
import Evaluator.Syntax

import Size.Deeds

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
--


{-# INLINE split #-}
split :: MonadStatics m
      => Generaliser
      -> ((Deeds, State) -> m (Deeds, Out FVedTerm))
      -> (Deeds, State)
      -> m (Deeds, Out FVedTerm) -- NB: it is very important that extra_statics go in the second argument of union, because we don't want them overriding real definitions in the heap!
split gen opt (deeds, s) = optimiseSplit opt deeds' bracketeds_heap bracketed_focus
  where (deeds', bracketeds_heap, bracketed_focus) = simplify gen (deeds, s)


-- Non-expansive simplification that we can safely do just before splitting to make the splitter a bit simpler
data QA = Question Var
        | Answer   (ValueF Anned)


{-# INLINE simplify #-}
simplify :: Generaliser
         -> (Deeds, State)
         -> (Deeds, M.Map (Out Var) (Bracketed State), Bracketed State)
simplify gen (init_deeds, init_s)
  = (\res@(deeds', bracketed_heap, bracketed) -> assertRender (text "simplify: deeds lost or gained") (not dEEDS || noGain (init_deeds `releaseStateDeed` init_s) (M.fold (flip (releaseBracketedDeeds releaseStateDeed)) (releaseBracketedDeeds releaseStateDeed deeds' bracketed) bracketed_heap)) res) $
    go (init_deeds, init_s)
  where
    go (deeds, s@(Heap h ids, k, (rn, e)))
         -- If we can find some fraction of the stack or heap to drop that looks like it will be admissable, just residualise those parts and continue
        | Just split_from <- seekAdmissable h named_k, (ids', ctxt_id) <- stepIdSupply ids  = splitt split_from (deeds, (Heap h ids', named_k, ([],                                                     oneBracketed (Once ctxt_id, \ids -> (Heap M.empty ids, [], (rn, e))))))
         -- We can't step past a variable or value, because if we do so I can't prove that simplify terminates and the sc recursion has finite depth
        | Just qa <- toQA (annee e),                   (ids1, ids2)    <- splitIdSupply ids = splitt bottom     (deeds, (Heap h ids1, named_k, (case qa of Question x -> [rename rn x]; Answer _ -> [], splitQA ids2 (rn, qa))))
         -- Otherwise, keep dropping stuff until one of the two conditions above holds
        | Just (deeds', s') <- step (deeds, s)                                              = trace ("simplify: dropping " ++ droppingWhat (annee (snd (thd3 s))) ++ " piece :(") $ go (deeds', s')
         -- Even if we can never find some admissable fragment of the input, we *must* eventually reach a variable or value
        | otherwise                                                                         = error "simplify: could not stop or step!"
      where named_k = [0..] `zip` k
    
    droppingWhat (App _ _)    = "App"
    droppingWhat (PrimOp _ _) = "Primop"
    droppingWhat (Case _ _)   = "Case"
    droppingWhat (LetRec _ _) = "LetRec"
    
    toQA (Var x)   = Just (Question x)
    toQA (Value v) = Just (Answer v)
    toQA _ = Nothing
    
    seekAdmissable :: PureHeap -> NamedStack -> Maybe (IS.IntSet, S.Set (Out Var))
    seekAdmissable h named_k = traceRender ("gen_kfs", gen_kfs, "gen_xs'", gen_xs') $ guard (not (IS.null gen_kfs) || not (S.null gen_xs')) >> Just (traceRender ("seekAdmissable", gen_kfs, gen_xs') (gen_kfs, gen_xs'))
      where gen_kfs = IS.fromList [i  | (i, kf) <- named_k, generaliseStackFrame gen kf]
            gen_xs' = S.fromList  [x' | (x', hb) <- M.toList h, generaliseHeapBinding gen x' hb]


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

releaseBracketedDeeds :: (Deeds -> a -> Deeds) -> Deeds -> Bracketed a -> Deeds
releaseBracketedDeeds release deeds b = foldl' release deeds (fillers b)

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
                  => ((Deeds, State) -> m (Deeds, Out FVedTerm))
                  -> (Deeds, Bracketed (Deeds, State))
                  -> m (Deeds, Out FVedTerm)
optimiseBracketed opt (deeds, b) = do
    (deeds, es') <- optimiseMany (\(deeds, (s_deeds, s)) -> opt (deeds `releaseDeedsTo` s_deeds, s)) (deeds, fillers b)
    return (deeds, rebuild b es')


transformWholeList :: ([a] -> [b]) -- Transformer of concatenated lists -- must be length-preserving!
                   -> [a] -> [[a]] -- Unconcatenated list structures to transform
                   -> ([b], [[b]]) -- Unconcatenated result of transformation
transformWholeList f xs yss = (xs', yss')
  where ys = concat yss
        zs0 = f (xs ++ ys)
        (xs', zs1) = splitBy xs zs0
        (ys', [])  = splitBy ys zs1
        yss' = splitManyBy yss ys'

optimiseSplit :: MonadStatics m
              => ((Deeds, State) -> m (Deeds, Out FVedTerm))
              -> Deeds
              -> M.Map (Out Var) (Bracketed State)
              -> Bracketed State
              -> m (Deeds, Out FVedTerm)
optimiseSplit opt deeds bracketeds_heap bracketed_focus = do
    -- 0) The "process tree" splits at this point. We can choose to distribute the deeds between the children in a number of ways
    let stateSize (h, k, in_e) = heapSize h + stackSize k + termSize (snd in_e)
          where heapBindingSize hb = case hb of
                    Environmental   -> 0
                    Updated _ _     -> 0
                    Phantom _       -> 0
                    Concrete (_, e) -> termSize e
                heapSize (Heap h _) = sum (map heapBindingSize (M.elems h))
                stackSize = sum . map stackFrameSize
                stackFrameSize kf = 1 + case kf of
                    Apply x'                -> varSize x'
                    Scrutinise in_alts      -> sum (map altSize' (snd in_alts))
                    PrimApply _ in_vs in_es -> sum (map (valueSize . snd) in_vs) + sum (map (termSize . snd) in_es)
                    Update x'               -> varSize x'
        bracketSizes = map stateSize . fillers
        
        (heap_xs, bracketeds_heap_elts) = unzip (M.toList bracketeds_heap)
        -- NB: it is *very important* that the list supplied to apportion contains at least one element and at least one non-zero weight, or some
        -- deeds will vanish in a puff of digital smoke. We deal with this in the proportional case by padding the input list with a 1
        (deeds_initial:deeds_focus, deedss_heap)
          | Proportional <- dEEDS_POLICY = transformWholeList (apportion deeds) (1 : bracketSizes bracketed_focus) (map bracketSizes bracketeds_heap_elts)
          | otherwise                    = (deeds : [deeds_empty | _ <- bracketSizes bracketed_focus], [[deeds_empty | _ <- bracketSizes b] | b <- bracketeds_heap_elts])
            where deeds_empty = mkEmptyDeeds deeds
        
        bracketeds_deeded_heap = M.fromList (heap_xs `zip` zipWith (\deeds_heap -> modifyFillers (deeds_heap `zip`)) deedss_heap bracketeds_heap_elts)
        bracketed_deeded_focus = modifyFillers (deeds_focus `zip`) bracketed_focus
    
    assertRenderM (text "optimiseSplit: deeds lost or gained!") (not dEEDS || noChange (M.fold (flip (releaseBracketedDeeds releaseStateDeed)) (releaseBracketedDeeds releaseStateDeed deeds bracketed_focus) bracketeds_heap)
                                                                                       (M.fold (flip (releaseBracketedDeeds (\deeds (extra_deeds, s) -> extra_deeds `releaseDeedsTo` releaseStateDeed deeds s))) (releaseBracketedDeeds (\deeds (extra_deeds, s) -> extra_deeds `releaseDeedsTo` releaseStateDeed deeds s) deeds_initial bracketed_deeded_focus) bracketeds_deeded_heap))
    
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
    return (foldl' (releaseBracketedDeeds (\deeds (s_deeds, s) -> s_deeds `releaseDeedsTo` releaseStateDeed deeds s)) leftover_deeds (M.elems bracketeds_deeded_heap),
            letRecSmart xes e_focus)
  where
    -- TODO: clean up this incomprehensible loop
    -- TODO: investigate the possibility of just fusing in the optimiseLetBinds loop with this one
    go hes extra_statics leftover_deeds bracketeds_deeded_heap xes fvs = do
        let extra_statics' = extra_statics `S.union` S.fromList (map fst hes) -- NB: the statics already include all the binders from bracketeds_deeded_heap, so no need to add xes stuff
        (hes', (leftover_deeds, bracketeds_deeded_heap, fvs, xes')) <- bindCapturedFloats extra_statics' $ optimiseLetBinds opt leftover_deeds bracketeds_deeded_heap (fvs `S.union` S.unions (map (fvedTermFreeVars . snd) hes)) -- TODO: no need to get FVs in this way (they are in Promise)
        (if null hes' then (\a b c d -> return (a,b,c,d)) else go hes' extra_statics') leftover_deeds bracketeds_deeded_heap (xes ++ hes ++ xes') fvs


-- We only want to drive (and residualise) as much as we actually refer to. This loop does this: it starts
-- by residualising the free variables of the focus residualisation (or whatever is in the let body),
-- and then transitively inlines any bindings whose corresponding binders become free.
optimiseLetBinds :: MonadStatics m
                 => ((Deeds, State) -> m (Deeds, Out FVedTerm))
                 -> Deeds
                 -> M.Map (Out Var) (Bracketed (Deeds, State))
                 -> FreeVars
                 -> m (Deeds, M.Map (Out Var) (Bracketed (Deeds, State)), FreeVars, Out [(Var, FVedTerm)])
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

type NamedStack = [(Int, StackFrame)]

splitt :: (IS.IntSet, S.Set (Out Var))
       -> (Deeds, (Heap, NamedStack, ([Out Var], Bracketed (Entered, IdSupply -> State))))         -- ^ The thing to split, and the Deeds we have available to do it
       -> (Deeds,                             -- ^ The Deeds still available after splitting
           M.Map (Out Var) (Bracketed State), -- ^ The residual "let" bindings
           Bracketed State)                   -- ^ The residual "let" body
splitt (gen_kfs, gen_xs) (old_deeds, (cheapifyHeap . (old_deeds,) -> (deeds, Heap h (splitIdSupply -> (ids_brack, ids))), named_k, (scruts, bracketed_qa)))
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
    split_fp = lfpFrom S.empty (fst . split_step)
    
    -- Simultaneously computes the next fixed-point step and some artifacts computed along the way,
    -- which happen to correspond to exactly what I need to return from splitt.
    split_step not_resid_xs = -- let pPrintBracketedState = map residualiseState . fillers in traceRender ("split_step", (not_resid_xs, bound_xs S.\\ not_resid_xs), pureHeapBoundVars h_not_residualised, pureHeapBoundVars h_residualised, M.map pPrintBracketedState bracketeds_heap', pPrintBracketedState bracketed_focus') $
                              (not_resid_xs', (deeds2, bracketeds_heap', bracketed_focus'))
      where
        -- 0) Infer the stack frames that I'm not residualising based on the *variables* I'm not residualising
        not_resid_kfs = IS.fromList [i | (i, kf) <- named_k
                                       , i `IS.notMember` gen_kfs
                                       , case kf of Update (annee -> x') -> x' `S.member` not_resid_xs
                                                    _                    -> True
                                       ]
        
        -- 1) Build a candidate splitting for the Stack and QA components
        -- When creating the candidate stack split, we ensure that we create a residual binding
        -- for any variable in the resid_xs set, as we're not going to inline it to continue.
        --
        -- We also take this opportunity to fill in the IdSupply required by each prospective new State.
        -- We can use the same one for each context because there is no danger of shadowing.
        fill_ids :: Bracketed (Entered, IdSupply -> State) -> Bracketed (Entered, State)
        fill_ids = fmap (\(ent, f) -> (ent, f ids_brack))
        (deeds0_unreleased, bracketeds_updated, bracketed_focus)
          = (\(a, b, c) -> (a, M.map (second fill_ids) b, fill_ids c)) $
            pushStack ids deeds scruts [(i `IS.member` not_resid_kfs, kf) | (i, kf) <- named_k] bracketed_qa
        
        -- 2) Build a splitting for those elements of the heap we propose to residualise not in not_resid_xs
        (h_not_residualised, h_residualised) = M.partitionWithKey (\x' _ -> x' `S.member` not_resid_xs) h
        bracketeds_nonupdated = M.mapMaybeWithKey (\x' hb -> do { Concrete in_e <- return hb; return (Phantom in_e, fill_ids $ oneBracketed (Once (fromJust (name_id x')), \ids -> (Heap M.empty ids, [], in_e))) }) h_residualised
        -- For every heap binding we ever need to deal with, contains:
        --  1) A phantom version of that heap binding
        --  2) A version of that heap binding as a concrete Bracketed thing
        bracketeds_heap = bracketeds_updated `M.union` bracketeds_nonupdated
        
        -- 3) Inline as much of the Heap as possible into the candidate splitting
        
        -- 3a) Release deeds
        -- In order to make the Deeds-based stuff less conservative, my first action here is to release our claims to those deeds
        -- which we do *not* intend to create a residual let binding for here and now. This will let us always inline a heap-bound
        -- thing into *at least one* context (unless it really is referred to by the residual code).
        --
        -- The equivalent process is done for the stack in splitStack itself: we just subtract 1 from the number of deeds we need to
        -- claim when duplicating a stack frame.
        --
        -- FIXME: I'm pretty sure things will go wrong if we run out of deeds. In particular, we may duplicate some deeds because
        -- we will have released deeds for everything in h_non_residualised, but those bindings will still be free in some of the things
        -- they were transitivelyInlined into, if deed acquisition failed. This means that optimiseSplit will create bindings for them
        -- without paying for those bindings!
        -- I think that in fixing this I could ensure that the outgoing bracketeds_heap' excludes all those things in not_resid_xs.
        -- After all, IIRC the only reason it doesn't at the moment is because I want to catch those bindings we wanted to push down
        -- but actually couldn't because of deeds issues.
        deeds0 = M.fold (flip releaseHeapBindingDeeds) deeds0_unreleased h_not_residualised
        
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
        h_inlineable = (h_not_residualised `M.union`         -- Take any non-residualised bindings from the input heap/stack...
                        h_cheap_and_phantom `M.union`        -- ...failing which, take concrete definitions for cheap heap bindings even if they are also residualised...
                        M.map fst bracketeds_heap) `exclude` -- ...failing which, take a phantom version of the remaining non-residualised heap/stack bindings
                        gen_xs                               -- The exclusion just makes sure we don't inline explicitly generalised bindings (even phantom ones)
        
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
        inlineBracketHeap :: Deeds -> Bracketed (Entered, State) -> (Deeds, EnteredEnv, Bracketed State)
        inlineBracketHeap = inlineHeapT (\deeds (ent, state) -> case transitiveInline h_inlineable (deeds, state) of (deeds', state') -> (deeds', mkEnteredEnv ent $ stateFreeVars state', state'))
        
        -- 3c) Actually do the inlining of as much of the heap as possible into the proposed floats
        -- We also take this opportunity to strip out the Entered information from each context.
        (deeds1, entered_focus, bracketed_focus') =             inlineBracketHeap deeds0            bracketed_focus
        (deeds2, entered_heap,  bracketeds_heap') = inlineHeapT inlineBracketHeap deeds1 (M.map snd bracketeds_heap)

        -- 4) Construct the next element of the fixed point process:
        --  a) We should residualise:
        --     * Any x in the extraFvs of a bracketed thing, because we need to be able to refer to it right here, whatever happens
        --     * Anything explicitly generalised
        must_resid_xs = extraFvs bracketed_focus' `S.union` S.unions (map extraFvs (M.elems bracketeds_heap'))
                          `S.union` gen_xs
        --  b) Lastly, we should *stop* residualising bindings that got Entered only once in the proposal.
        --     I once thought that we should only add a single variable to non_resid_xs' every time around the loop, because I worried
        --     that choosing not to residualise some binding would cause some other bindings to stop being candiates (i.e. would increase
        --     the number of times they were entered).
        --
        --     However, I've revised my opinion and decided to add all candidate variables every time. This is because if we inline a binding
        --     into a context where it is still evaluated Once, anything it refers to is still evaluated Once. So the existing Entered information
        --     does not appear to be invalidated when we decide not to residualise an additional binding.
        entered    = entered_focus `join` entered_heap
        not_resid_xs' = -- traceRender ("candidates", onces, must_resid_xs, not_resid_xs, candidates S.\\ not_resid_xs) $
                        not_resid_xs `S.union` candidates
          where onces = S.filter (\x' -> maybe True isOnce (M.lookup x' entered)) bound_xs
                candidates = onces S.\\ must_resid_xs
    
    -- Bound variables: those variables that I am interested in making a decision about whether to residualise or not
    bound_xs = pureHeapBoundVars h `S.union` stackBoundVars (map snd named_k)
    
    -- Heap full of cheap expressions and any phantom stuff from the input heap.
    -- Used within the main loop in the process of computing h_inlineable -- see comments there for the full meaning of this stuff.
    extract_cheap_hb (Concrete (rn, e)) = guard (isCheap (annee e)) >> Just (Concrete (rn, e))
    extract_cheap_hb hb                 = Just hb -- Inline phantom stuff verbatim: there is no work duplication issue
    h_cheap_and_phantom = M.mapMaybe extract_cheap_hb h


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
transitiveInline :: PureHeap -> (Deeds, State) -> (Deeds, State)
transitiveInline init_h_inlineable (deeds, (Heap h ids, k, in_e))
    = -- (if not (S.null not_inlined_vs') then traceRender ("transitiveInline: generalise", not_inlined_vs') else id) $
      -- traceRender ("transitiveInline", pureHeapBoundVars init_h_inlineable, state_fvs, pureHeapBoundVars h') $
      (deeds', (Heap h' ids, k, in_e))
  where
    state_fvs = stateFreeVars (Heap M.empty ids, k, in_e)
    (deeds', h') = go 0 deeds (init_h_inlineable `M.union` h) M.empty (mkConcreteLiveness state_fvs) -- FIXME: at the moment it looks like I assume I don't have the deeds for this heap
    
    -- NB: in the presence of phantoms, this loop gets weird.
    --  1. We want to inline phantoms if they occur as free variables of the state, so we get staticness
    --  2. We want to inline phantoms if they ocucr as free variables of inlined phantoms, so we get to see chains of staticness
    --    arising from e.g. foldl', hence allowing us to do intelligent staticness generalisation
    --  3. We want to inline phantom versions of non-phantom definitions if they occur as free variables of inlined phantoms
    --  4. If we inlined something according to criteria 3. and that definition later becomes a free variable of a non-phantom,
    --     we need to make sure that phantom definition is replaced with a real one
    go :: Int -> Deeds -> PureHeap -> PureHeap -> Liveness -> (Deeds, PureHeap)
    go n deeds h_inlineable h_output live
      = -- traceRender ("go", n, M.keysSet h_inlineable, M.keysSet h_output, fvs) $
        if live == live'
        then (deeds', h_output') -- NB: it's important we use the NEW versions of h_output/deeds, because we might have inlined extra stuff even though live hasn't changed!
        else go (n + 1) deeds' h_inlineable' h_output' live' -- NB: the argument order to union is important because we want to overwrite an existing phantom binding (if any) with the concrete one
      where 
        (deeds', h_inlineable', h_output', live') = M.foldWithKey consider_inlining (deeds, M.empty, h_output, live) h_inlineable
        
        -- NB: we rely here on the fact that our caller will still be able to fill in bindings for stuff from h_inlineable
        -- even if we choose not to inline it into the State, and that such bindings will not be evaluated until they are
        -- actually demanded (or we could get work duplication by inlining into only *some* Once contexts).
        --
        -- NB: we also rely here on the fact that the original h contains "optional" bindings in the sense that they are shadowed
        -- by something bound above - i.e. it just tells us how to unfold case scrutinees within a case branch.
        consider_inlining x' hb (deeds, h_inlineable, h_output, live)
          | Just why_live <- x' `whyLive` live -- Is the binding actually live?
          , (deeds, h_inlineable, inline_hb) <- case hb of
              Concrete in_e@(_, e) -> case why_live of
                ConcreteLive -> case claimDeed deeds (annedTag e) of -- Do we have enough deeds to inline a concrete version at all?
                                                Just deeds -> (deeds,                h_inlineable, hb)
                                                Nothing    -> (deeds, M.insert x' hb h_inlineable, Phantom in_e)
                PhantomLive  -> (deeds, M.insert x' hb h_inlineable, Phantom in_e) -- We want to inline only a *phantom* version if the binding is demanded by phantoms only, or madness ensues
              _              -> (deeds, h_inlineable, hb)
          = (deeds, h_inlineable, M.insert x' inline_hb h_output, live `plusLiveness` heapBindingLiveness inline_hb)
          | otherwise
          = (deeds, M.insert x' hb h_inlineable, h_output, live)


-- TODO: replace with a genuine evaluator. However, think VERY hard about the termination implications of this!
-- I think we can only do it when the splitter is being invoked by a non-whistling invocation of sc.
cheapifyHeap :: (Deeds, Heap) -> (Deeds, Heap)
cheapifyHeap deedsheap | not sPLITTER_CHEAPIFICATION = deedsheap
cheapifyHeap (deeds, Heap h (splitIdSupply -> (ids, ids'))) = (deeds', Heap (M.map Concrete (M.fromList floats) `M.union` h') ids')
  where
    ((deeds', _, floats), h') = M.mapAccum (\(deeds, ids, floats0) hb -> case hb of Concrete in_e -> (case cheapify deeds ids in_e of (deeds, ids, floats1, in_e') -> ((deeds, ids, floats0 ++ floats1), Concrete in_e')); _ -> ((deeds, ids, floats0), hb)) (deeds, ids, []) h
    
    -- TODO: make cheapification more powerful (i.e. deal with case bindings)
    cheapify :: Deeds -> IdSupply -> In AnnedTerm -> (Deeds, IdSupply, [(Out Var, In AnnedTerm)], In AnnedTerm)
    cheapify deeds0 ids0 (rn, annedTag &&& annee -> (tg, LetRec xes e)) = (deeds3, ids3, zip in_xs in_es' ++ floats0 ++ floats1, in_e')
      where deeds1 = releaseDeedDescend_ deeds0 tg
            (        ids1, rn', unzip -> (in_xs, in_es)) = renameBounds (\_ x' -> x') ids0 rn xes
            (deeds2, ids2, floats0, in_es') = cheapifyMany deeds1 ids1 in_es
            (deeds3, ids3, floats1, in_e')  = cheapify deeds2 ids2 (rn', e)
    cheapify deeds ids in_e = (deeds, ids, [], in_e)

    cheapifyMany :: Deeds -> IdSupply -> [In AnnedTerm] -> (Deeds, IdSupply, [(Out Var, In AnnedTerm)], [In AnnedTerm])
    cheapifyMany deeds ids = reassociate . mapAccumL ((associate .) . uncurry cheapify) (deeds, ids)
      where reassociate ((deeds, ids), unzip -> (floatss, in_es)) = (deeds, ids, concat floatss, in_es)
            associate (deeds, ids, floats, in_e) = ((deeds, ids), (floats, in_e))


pushStack :: IdSupply
          -> Deeds
          -> [Out Var]
          -> [(Bool, StackFrame)]
          -> Bracketed (Entered, IdSupply -> State)
          -> (Deeds,
              M.Map (Out Var) (HeapBinding, Bracketed (Entered, IdSupply -> State)),
              Bracketed (Entered, IdSupply -> State))
pushStack _   deeds _      []                 bracketed_hole = (deeds, M.empty, bracketed_hole)
pushStack ids deeds scruts ((may_push, kf):k) bracketed_hole = second3 (`M.union` bracketed_heap') $ pushStack ids2 deeds' scruts' k bracketed_hole'
  where
    (ids1, ids2) = splitIdSupply ids

    -- If we have access to hole tail positions, we should try to inline this stack frame into that tail position.
    -- If we do not have access to the tail positions of the hole, all we can do is rebuild a bit of residual syntax around the hole.
    (deeds', (scruts', bracketed_heap', bracketed_hole'))
      = (guard may_push >> fmap (\(deeds', bracketed_hole') -> (deeds', ([], M.empty, bracketed_hole'))) (pushStackFrame kf deeds bracketed_hole)) `orElse`
        (deeds, splitStackFrame ids1 kf scruts bracketed_hole)

pushStackFrame :: StackFrame
               -> Deeds
               -> Bracketed (Entered, IdSupply -> State)
               -> Maybe (Deeds, Bracketed (Entered, IdSupply -> State))
pushStackFrame kf deeds bracketed_hole = do
    (Just deeds', bracketed_hole') <- modifyTails push bracketed_hole
    return (deeds', bracketed_hole')
  where
    -- Inline parts of the evaluation context into each branch only if we can get that many deeds for duplication
    push fillers = case foldM (\deeds tag -> claimDeeds deeds tag (branch_factor - 1)) deeds (stackFrameTags kf) of -- NB: subtract one because one occurrence is already "paid for". It is OK if the result is negative (i.e. branch_factor 0)!
            Nothing    -> traceRender ("pushStackFrames: deed claim failure", branch_factor) (Nothing, fillers)
            Just deeds -> (Just deeds, map (\(ent, f) -> (ent, second3 (++ [kf]) . f)) fillers)
      where branch_factor = length fillers

splitStackFrame :: IdSupply
                -> StackFrame
                -> [Out Var]
                -> Bracketed (Entered, IdSupply -> State)
                -> ([Out Var],
                    M.Map (Out Var) (HeapBinding, Bracketed (Entered, IdSupply -> State)),
                    Bracketed (Entered, IdSupply -> State))
splitStackFrame ids kf scruts bracketed_hole
  | Update x' <- kf = splitUpdate scruts x' bracketed_hole
  | otherwise = ([], M.empty, case kf of
    Apply (annee -> x2') -> zipBracketeds (\[e] -> e `app` x2') (\[fvs] -> S.insert x2' fvs) [id] (\_ -> Nothing) [bracketed_hole]
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    -- (if not (null k_not_inlined) then traceRender ("splitStack: generalise", k_not_inlined) else id) $
                                                    zipBracketeds (\(e_hole:es_alts) -> case_ e_hole (alt_cons' `zip` es_alts)) (\(fvs_hole:fvs_alts) -> fvs_hole `S.union` S.unions (zipWith (S.\\) fvs_alts alt_bvss)) (id:[\bvs -> bvs S.\\ alt_bvs | alt_bvs <- alt_bvss]) (\(_tails_hole:tailss_alts) -> liftM concat (sequence tailss_alts)) (bracketed_hole : bracketed_alts)
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
            alt_hs = zipWith3 (\alt_rn alt_con alt_tg -> M.fromList $ do { Just scrut_v <- [altConToValue alt_con]; scrut <- scruts; return (scrut, Concrete (alt_rn, annedTerm alt_tg (Value scrut_v))) }) alt_rns alt_cons (map annedTag alt_es) -- FIXME: should be grabbing deeds for these? Or rely on transitiveInline to get them for you?
            alt_bvss = map (\alt_con' -> fst $ altConOpenFreeVars alt_con' (S.empty, S.empty)) alt_cons'
            bracketed_alts = zipWith (\alt_h alt_in_e -> oneBracketed (Once ctxt_id, \ids -> (Heap alt_h ids, [], alt_in_e))) alt_hs alt_in_es
    PrimApply pop in_vs in_es -> zipBracketeds (primOp pop) S.unions (repeat id) (\_ -> Nothing) (bracketed_vs ++ bracketed_hole : bracketed_es)
      where -- 0) Manufacture context identifier
            (ids', state_idss) = accumL splitIdSupply ids (length in_es)
            ctxt_ids = map idFromSupply state_idss
            
            -- 1) Split every value and expression remaining apart
            bracketed_vs = map (splitValue ids' . fmap annee) in_vs
            bracketed_es  = zipWith (\ctxt_id in_e -> oneBracketed (Once ctxt_id, \ids -> (Heap M.empty ids, [], in_e))) ctxt_ids in_es)
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
splitUpdate :: [Out Var] -> Anned Var -> Bracketed (Entered, IdSupply -> State)
            -> ([Out Var], M.Map (Out Var) (HeapBinding, Bracketed (Entered, IdSupply -> State)), Bracketed (Entered, IdSupply -> State))
splitUpdate scruts x' bracketed_hole = (annee x' : scruts, M.singleton (annee x') (Updated (annedTag x') hole_fvs, bracketed_hole),
                                        oneBracketed (Once ctxt_id, \ids -> (Heap M.empty ids, [], (mkIdentityRenaming [annee x'], annedTerm (annedTag x') (Var (annee x'))))))
  where
    ctxt_id = fromJust (name_id (annee x'))
    hole_fvs = bracketedFreeVars (\(_, mk_state) -> stateFreeVars (mk_state matchIdSupply)) bracketed_hole
  -- TODO: we get poor generalisation for variables bound by update frames because we don't record proper tags or whatever for them
  --
  -- We could make this work using the Phantom constructor by threading in a rebuilt version of the term being updated, but at the moment that is
  -- tricky because stack frames are untagged, so rebuilding a tagged term is close to impossible.
  --
  -- So at the moment we do a "poor mans" thing and just keep track of the free variables and the tag in a new Updated constructor. As it turns out,
  -- this is all that is actually required to make generalisation work properly, although it might pessimise the matcher a tiny bit.

splitValue :: IdSupply -> In AnnedValue -> Bracketed (Entered, IdSupply -> State)
splitValue ids (rn, Lambda x e) = zipBracketeds (\[e'] -> lambda x' e') (\[fvs'] -> fvs') [S.insert x'] (\_ -> Nothing) [oneBracketed (Many, \ids -> (Heap M.empty ids, [], (rn', e)))]
  where (_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v             = noneBracketed (value v') (inFreeVars annedValueFreeVars' in_v)
  where v' = detagAnnedValue' $ renameIn renameAnnedValue' ids in_v

splitQA :: IdSupply -> In QA -> Bracketed (Entered, IdSupply -> State)
splitQA _   (rn, Question x) = noneBracketed (var x') (S.singleton x')
  where x' = rename rn x
splitQA ids (rn, Answer v)   = splitValue ids (rn, v)
