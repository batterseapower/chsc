{-# LANGUAGE PatternGuards, ViewPatterns, TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable,
             MultiParamTypeClasses, FlexibleInstances, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (StaticSort(..), Statics, staticVars, mkTopLevelStatics, extendStatics, isStatic, MonadStatics(..), split) where

--import Supercompile.Residualise

import Core.FreeVars
import Core.Renaming
import Core.Statics
import Core.Syntax

import Evaluator.Evaluate
import Evaluator.FreeVars
import Evaluator.Syntax

import Size.Deeds

import Termination.Generaliser

import Algebra.Lattice
import Name
import Renaming
import StaticFlags
import Utilities hiding (tails)

import Control.Applicative
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
      -> ((Deeds, Statics, State) -> m (Deeds, Out FVedTerm))
      -> (Deeds, Statics, State)
      -> m (Deeds, Out FVedTerm)
split gen opt (deeds, statics, s) = optimiseSplit (\extra_statics (deeds, s) -> opt (deeds, statics' `extendStatics` extra_statics, s)) deeds' bracketeds_heap bracketed_focus
  where (statics', (deeds', bracketeds_heap, bracketed_focus)) = simplify gen (deeds, statics, s)


-- Non-expansive simplification that we can safely do just before splitting to make the splitter a bit simpler
data QA = Question Var
        | Answer   (ValueF Anned)


{-# INLINE simplify #-}
simplify :: Generaliser
         -> (Deeds, Statics, State)
         -> (Statics, (Deeds, M.Map (Out Var) (Tagged (Bracketed State)), Bracketed State))
simplify (gen_split, gen_s) (init_deeds, statics, init_s)
  = (\res@(_, (deeds', bracketed_heap, bracketed)) -> assertRender (text "simplify: deeds lost or gained") (noGain (init_deeds `releaseStateDeed` init_s) (M.fold (flip (releaseBracketedDeeds releaseStateDeed) . tagee) (releaseBracketedDeeds releaseStateDeed deeds' bracketed) bracketed_heap)) res) $
    go (init_deeds, init_s) -- FIXME: use gen_split
  where
    go (deeds, s@(Heap h ids, k, (rn, e)))
         -- We can't step past a variable or value, because if we do so I can't prove that simplify terminates and the sc recursion has finite depth
         -- If the termination criteria has not hit, we
        | Just qa <- toQA (annee e),                   (ids1, ids2)    <- splitIdSupply ids = (statics,  splitt bottom     (deeds, (Heap h ids1, named_k, (case qa of Question x -> [rename rn x]; Answer _ -> [], splitQA ids2 (rn, qa)))))
         -- If we can find some fraction of the stack or heap to drop that looks like it will be admissable, just residualise those parts and continue
        | Just split_from <- seekAdmissable h named_k, (ids', ctxt_id) <- stepIdSupply ids  = (statics,  splitt split_from (deeds, (Heap h ids', named_k, ([],                                                     oneBracketed (Once ctxt_id, \ids -> (Heap M.empty ids, [], (rn, e)))))))
         -- If we can find some static variables to drop that look like they will improve the situation, generalise them away
        | Just statics' <- admissableStatics                                                = (statics', (deeds, M.empty, oneBracketed s))
         -- Otherwise, keep dropping stuff until one of the two conditions above holds
        | Just (_, deeds', s') <- step (const id) emptyFreeVars (emptyLosers, deeds, s)     = trace ("simplify: dropping " ++ droppingWhat (annee (snd (thd3 s))) ++ " piece :(") $ go (deeds', s')
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
    
    admissableStatics :: Maybe Statics
    admissableStatics = guard (gENERALISE_STATICS && not (M.null removed_static_vars)) >> return (Statics static_vars')
      where (removed_static_vars, static_vars') = M.partitionWithKey (\x' static_sort -> generaliseStaticVar gen_split x' static_sort) (staticVars statics)
    
    seekAdmissable :: PureHeap -> NamedStack -> Maybe (IS.IntSet, S.Set (Out Var))
    seekAdmissable h named_k = traceRender ("gen_kfs", gen_kfs, "gen_xs'", gen_xs') $ guard (not (IS.null gen_kfs) || not (S.null gen_xs')) >> Just (traceRender ("seekAdmissable", gen_kfs, gen_xs') (gen_kfs, gen_xs'))
      where gen_kfs = IS.fromList [i  | (i, kf) <- named_k, generaliseStackFrame gen_s kf]
            gen_xs' = S.fromList  [x' | (x', in_e) <- M.toList h, generaliseHeapBinding gen_s x' in_e]


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
    rebuild :: [Out FVedTerm] -> Out FVedTerm,        -- Rebuild the full output term given outputs to plug into each hole
    extraFvs :: FreeVars,                      -- Maximum free variables added by the residual wrapped around the holes
    transfer :: [FreeVars] -> FreeVars, -- Strips any variables bound by the residual out of the hole FVs
    fillers :: [a],                                   -- Hole-fillers themselves. Usually State
    tails :: Maybe [Int]                              -- The indexes of all holes in tail position. If this is not Nothing, this is an *exhaustive* list of possible tail positions.
  } deriving (Functor)

instance Foldable.Foldable Bracketed where
    foldMap f = Foldable.foldMap f . fillers

instance Traversable.Traversable Bracketed where
    traverse f (Bracketed a b c d e) = (\d' -> Bracketed a b c d' e) <$> Traversable.traverse f d

instance Accumulatable Bracketed where
    mapAccumTM f acc b = liftM (\(acc', fillers') -> (acc', b { fillers = fillers' })) $ mapAccumTM f acc (fillers b)

noneBracketed :: Out FVedTerm -> FreeVars -> Bracketed a
noneBracketed a b = Bracketed {
    rebuild  = \[] -> a,
    extraFvs = b,
    transfer = \[] -> emptyFreeVars,
    fillers  = [],
    tails    = Nothing
  }

oneBracketed :: a -> Bracketed a
oneBracketed x = Bracketed {
    rebuild  = \[e] -> e,
    extraFvs = emptyFreeVars,
    transfer = \[fvs] -> fvs,
    fillers  = [x],
    tails    = Just [0]
  }

zipBracketeds :: ([Out FVedTerm] -> Out FVedTerm)
              -> ([FreeVars] -> FreeVars)
              -> ([FreeVars] -> FreeVars)
              -> ([Maybe [Int]] -> Maybe [Int])
              -> [Bracketed a]
              -> Bracketed a
zipBracketeds a b c d bracketeds = Bracketed {
      rebuild  = \(splitManyBy xss -> ess') -> a (zipWith rebuild bracketeds ess'),
      extraFvs = b (map extraFvs bracketeds),
      transfer = \(splitManyBy xss -> fvss) -> c (zipWith transfer bracketeds fvss),
      fillers  = concat xss,
      tails    = d $ snd $ foldl (\(i, tailss) bracketed -> (i + length (fillers bracketed), tailss ++ [fmap (map (+ i)) (tails bracketed)])) (0, []) bracketeds
    }
  where xss = map fillers bracketeds

bracketedFreeVars :: (a -> FreeVars) -> Bracketed a -> FreeVars
bracketedFreeVars fvs bracketed = extraFvs bracketed `unionFreeVars` transfer bracketed (map fvs (fillers bracketed))

releaseBracketedDeeds :: (Deeds -> a -> Deeds) -> Deeds -> Bracketed a -> Deeds
releaseBracketedDeeds release deeds b = foldl' release deeds (fillers b)

modifyFillers :: ([a] -> [b]) -> Bracketed a -> Bracketed b
modifyFillers f bracketed = Bracketed {
    rebuild = rebuild bracketed,
    extraFvs = extraFvs bracketed,
    transfer = transfer bracketed,
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
              => (M.Map (Out Var) StaticSort -> (Deeds, State) -> m (Deeds, Out FVedTerm))
              -> Deeds
              -> M.Map (Out Var) (Tagged (Bracketed State))
              -> Bracketed State
              -> m (Deeds, Out FVedTerm)
optimiseSplit opt deeds bracketeds_heap bracketed_focus = do
    -- 0) The "process tree" splits at this point. We can choose to distribute the deeds between the children in a number of ways
    let stateSize (h, k, in_e) = heapSize h + stackSize k + termSize (snd in_e)
          where heapSize (Heap h _) = sum (map (termSize . snd) (M.elems h))
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
          | Proportional <- dEEDS_POLICY = transformWholeList (apportion deeds) (1 : bracketSizes bracketed_focus) (map (bracketSizes . tagee) bracketeds_heap_elts)
          | otherwise                    = (deeds : [deeds_empty | _ <- bracketSizes bracketed_focus], [[deeds_empty | _ <- bracketSizes (tagee b)] | b <- bracketeds_heap_elts])
            where deeds_empty = mkEmptyDeeds deeds
        
        bracketeds_deeded_heap = M.fromList (heap_xs `zip` zipWith (\deeds_heap -> fmap (modifyFillers (deeds_heap `zip`))) deedss_heap bracketeds_heap_elts)
        bracketed_deeded_focus = modifyFillers (deeds_focus `zip`) bracketed_focus
    
    assertRenderM (text "optimiseSplit: deeds lost or gained!") (noChange (M.fold (flip (releaseBracketedDeeds releaseStateDeed) . tagee) (releaseBracketedDeeds releaseStateDeed deeds bracketed_focus) bracketeds_heap)
                                                                          (M.fold (flip (releaseBracketedDeeds (\deeds (extra_deeds, s) -> extra_deeds `releaseDeedsTo` releaseStateDeed deeds s)) . tagee) (releaseBracketedDeeds (\deeds (extra_deeds, s) -> extra_deeds `releaseDeedsTo` releaseStateDeed deeds s) deeds_initial bracketed_deeded_focus) bracketeds_deeded_heap))
    
    -- 1) Recursively drive the focus itself
    -- FIXME: fix comments below
    --
    -- NB: it is *very important* that we do not mark generalised variables as static! If we do, we defeat the whole point of
    -- generalisation because our specialisations do not truly become more "general", and simple things like foldl specialisation break.
    --
    -- NB: by the same token, it is also *very very important* that if a variable is generalised, we still bind here and now any "h" functions
    -- that refer to the generalised variable. If we just naively did (statics S.\\ gen_xs) for the statics set, we would break this. Instead, we
    -- need to make sure that the gen_xs *are removed entirely* from the statics set in the monad environment (the dangerous case is if the variable
    -- is already in there, which can be caused by shadowing induced by value duplication).
    let extra_statics = M.map (LocalVariable . tag) bracketeds_heap
    (hes, (leftover_deeds, e_focus)) <- bindCapturedFloats (M.keysSet extra_statics) $ optimiseBracketed (opt extra_statics) (deeds_initial, bracketed_deeded_focus)
    
    -- 2) We now need to think about how we are going to residualise the letrec. In fact, we need to loop adding
    -- stuff to the letrec because it might be the case that:
    --  * One of the hes from above refers to some heap binding that is not referred to by the let body
    --  * So after we do withStatics above we need to drive some element of the bracketeds_heap
    --  * And after driving that we find in our new hes a new h function referring to a new free variable
    --    that refers to some binding that is as yet unbound...
    (leftover_deeds, bracketeds_deeded_heap, xes) <- go hes extra_statics leftover_deeds bracketeds_deeded_heap [] (fvedTermFreeVars e_focus)
    
    -- 3) Combine the residualised let bindings with the let body
    return (foldl' (releaseBracketedDeeds (\deeds (s_deeds, s) -> s_deeds `releaseDeedsTo` releaseStateDeed deeds s)) leftover_deeds (map tagee $ M.elems bracketeds_deeded_heap),
            letRecSmart xes e_focus)
  where
    -- TODO: clean up this incomprehensible loop
    -- TODO: investigate the possibility of just fusing in the optimiseLetBinds loop with this one
    go hes extra_statics leftover_deeds bracketeds_deeded_heap xes fvs = do
        let extra_statics' = extra_statics `M.union` M.fromList [(x', HFunction) | (x', _) <- hes] -- NB: the statics already include all the binders from bracketeds_deeded_heap, so no need to add xes stuff
        (hes', (leftover_deeds, bracketeds_deeded_heap, fvs, xes')) <- bindCapturedFloats (M.keysSet extra_statics') $ optimiseLetBinds (opt extra_statics') leftover_deeds bracketeds_deeded_heap (fvs `unionFreeVars` unionsFreeVars (map (fvedTermFreeVars . snd) hes)) -- TODO: no need to get FVs in this way (they are in Promise)
        (if null hes' then (\a b c _d -> return (a,b,c)) else go hes' extra_statics') leftover_deeds bracketeds_deeded_heap (xes ++ hes ++ xes') fvs


-- We only want to drive (and residualise) as much as we actually refer to. This loop does this: it starts
-- by residualising the free variables of the focus residualisation (or whatever is in the let body),
-- and then transitively inlines any bindings whose corresponding binders become free.
optimiseLetBinds :: MonadStatics m
                 => ((Deeds, State) -> m (Deeds, Out FVedTerm))
                 -> Deeds
                 -> M.Map (Out Var) (Tagged (Bracketed (Deeds, State)))
                 -> FreeVars
                 -> m (Deeds, M.Map (Out Var) (Tagged (Bracketed (Deeds, State))), FreeVars, Out [(Var, FVedTerm)])
optimiseLetBinds opt leftover_deeds bracketeds_heap fvs' = traceRender ("optimiseLetBinds", M.keysSet bracketeds_heap, fvs') $
                                                           go leftover_deeds bracketeds_heap [] fvs'
  where
    go leftover_deeds bracketeds_deeded_heap_not_resid xes_resid resid_fvs
      | M.null h_resid = -- traceRenderM ("go", resid_fvs, resid_bvs, (M.map (residualiseBracketed (residualiseState . first3 (flip Heap prettyIdSupply))) bracketeds_deeded_heap)) $
                         return (leftover_deeds, bracketeds_deeded_heap_not_resid, resid_fvs, xes_resid)
      | otherwise = {- traceRender ("optimiseSplit", xs_resid') $ -} do
        -- Recursively drive the new residuals arising from the need to bind the resid_fvs
        (leftover_deeds, es_resid') <- optimiseMany (optimiseBracketed opt) (leftover_deeds, map tagee bracks_resid)
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
       -> (Deeds,                                        -- ^ The Deeds still available after splitting
           M.Map (Out Var) (Tagged (Bracketed State)),   -- ^ The residual "let" bindings
           Bracketed State)                              -- ^ The residual "let" body
splitt split_from (old_deeds, (cheapifyHeap . (old_deeds,) -> (deeds, Heap h (splitIdSupply -> (ids_brack, ids))), named_k, (scruts, bracketed_qa)))
    = -- traceRender ("splitt", residualiseHeap (Heap h ids_brack) (\ids -> residualiseStack ids k (case tagee qa of Question x' -> var x'; Answer in_v -> value $ detagTaggedValue $ renameIn renameTaggedValue ids in_v))) $
      snd $ split_step split_fp -- TODO: eliminate redundant recomputation here?
  where
    -- Note that as an optimisation, optimiseSplit will only actually creates those residual bindings if the
    -- corresponding variables are free *after driving*. Of course, we have no way of knowing which bindings
    -- will get this treatment here, so just treat resid_xs as being exactly the set of residualised stuff.
    split_fp = lfpFrom split_from (fst . split_step)
    
    -- Simultaneously computes the next fixed-point step and some artifacts computed along the way,
    -- which happen to correspond to exactly what I need to return from splitt.
    split_step (resid_kfs, resid_xs) = -- traceRender ("split_step", resid_xs, fvs', resid_xs') $
                                       ((resid_kfs', resid_xs'), (deeds2, bracketeds_heap', bracketed_focus'))
      where
        -- 1) Build a candidate splitting for the Stack and QA components
        -- When creating the candidate stack split, we ensure that we create a residual binding
        -- for any variable in the resid_xs set, as we're not going to inline it to continue.
        --
        -- We also take this opportunity to fill in the IdSupply required by each prospective new State.
        -- We can use the same one for each context because there is no danger of shadowing.
        fill_ids :: Bracketed (Entered, IdSupply -> State) -> Bracketed (Entered, State)
        fill_ids = fmap (\(ent, f) -> (ent, f ids_brack))
        (deeds0_unreleased, bracketeds_updated, bracketed_focus)
          = (\(a, b, c) -> (a, M.map (fmap fill_ids) b, fill_ids c)) $
            pushStack ids deeds scruts [(i `IS.notMember` resid_kfs, kf) | (i, kf) <- named_k] bracketed_qa
        
        -- 2) Build a splitting for those elements of the heap we propose to residualise in resid_xs
        (h_residualised, h_not_residualised) = M.partitionWithKey (\x' _ -> x' `S.member` resid_xs) h
        bracketeds_nonupdated = M.mapWithKey (\x' in_e -> Tagged (annedTag (snd in_e)) $ oneBracketed (Once (fromJust (name_id x')), (Heap M.empty ids_brack, [], in_e))) h_residualised
        bracketeds_heap = bracketeds_updated `M.union` bracketeds_nonupdated
        
        -- 3) Inline as much of the Heap as possible into the candidate splitting
        
        -- 3a) Release deeds
        -- In order to make the Deeds-based stuff less conservative, my first action here is to release our claims to those deeds
        -- which we do *not* intend to create a residual let binding for here and now. This will let us always inline a heap-bound
        -- thing into *at least one* context (unless it really is referred to by the residual code).
        --
        -- The equivalent process is done for the stack in splitStack itself: we just subtract 1 from the number of deeds we need to
        -- claim when duplicating a stack frame.
        deeds0 = M.fold (\(_, e) deeds -> releaseDeedDeep deeds (annedTag e)) deeds0_unreleased h_not_residualised
        
        -- 3b) Work out which part of the heap is admissable for inlining
        -- We are allowed to inline anything which is duplicatable or is not residualised right here and now
        h_cheap = M.filter (\(_, e) -> isCheap (annee e)) h
        h_inlineable = (h_not_residualised `M.union` h_cheap) `exclude` snd split_from -- FIXME: reduce hack value and explain??
        
        -- Generalising the final proposed floats may cause some bindings that we *thought* were going to be inlined to instead be
        -- residualised. We need to account for this in the Entered information (for work-duplication purposes), and in that we will
        -- also require any FVs of the new residualised things that are bound in the stack to residualise more frames.
        inlineHeapT :: Accumulatable t
                    => (Deeds -> a   -> (Deeds, FreeVarPaths, EnteredEnv, b))
                    ->  Deeds -> t a -> (Deeds, FreeVarPaths, EnteredEnv, t b)
        inlineHeapT f deeds b = (deeds', fvs_paths', entered', b')
          where ((deeds', fvs_paths', entered'), b') = mapAccumT (\(deeds, fvs_paths, entered) s -> case f deeds s of (deeds, fvs_paths', entered', s) -> ((deeds, M.unionWith (++) fvs_paths fvs_paths', entered `join` entered'), s)) (deeds, M.empty, bottom) b

        inlineBracketHeap :: Deeds -> Bracketed (Entered, State) -> (Deeds, FreeVarPaths, EnteredEnv, Bracketed State)
        inlineBracketHeap = inlineHeapT (`transitiveInline` h_inlineable)
        
        -- 3c) Actually do the inlining of as much of the heap as possible into the proposed floats
        -- We also take this opportunity to strip out the Entered information from each context.
        (deeds1, fvs_paths_focus', entered_focus, bracketed_focus') =                                                              inlineBracketHeap                        deeds0 bracketed_focus
        (deeds2, fvs_paths_heap',  entered_heap,  bracketeds_heap') = inlineHeapT (\deeds tged_x -> fourth4 (Tagged (tag tged_x)) (inlineBracketHeap deeds (tagee tged_x))) deeds1 bracketeds_heap

        -- 4) Construct the next element of the fixed point process:
        --  a) We should also residualise bindings that occur as free variables of any of the
        --     elements of the (post-inlining) residualised heap or focus. As a side effect, this will pick up
        --     any variables that should be residualised due to generalisation
        --  b) Lastly, we should residualise non-cheap bindings that got Entered more than once in the proposal
        --     to make the splitter more agressive (see Note [Better fixed points of Entered information]), I only
        --     do this for bindings that were actually direct free variables of the original term.
        fvs' = bracketedFreeVars stateFreeVars bracketed_focus' `S.union` S.unions [bracketedFreeVars stateFreeVars (tagee bracketed') | bracketed' <- M.elems bracketeds_heap']
        entered    = entered_focus `join` entered_heap
        fvs_paths' = M.unionWith (++) fvs_paths_focus' fvs_paths_heap'
        entered_resid_substep x' paths no_change@(newly_resid, not_newly_resid)
          = -- If *all* the paths leading here certainly don't contain something we are going to change our mind about residualising...
            if all (all (`S.member` not_newly_resid)) paths
            then -- ...and the binding is cheap or linear
                 if x' `M.member` h_cheap || maybe True isOnce (M.lookup x' entered)
                 then (newly_resid,             S.insert x' not_newly_resid) -- ...the binding is certainly not going to be residualised
                 else (S.insert x' newly_resid, not_newly_resid)             -- Otherwise, it certainly should be residualised to make a new root
            else no_change -- Can't decide yet
        entered_resid_step (nr, nnr) = -- traceRender ("entered_resid_step", (nr, nnr)) $
                                       M.foldWithKey entered_resid_substep (nr, nnr) fvs_paths'
        (newly_resid, _not_newly_resid) = -- traceRender ("entered_resid", fvs_paths') $
                                          lfpFrom (S.empty, M.keysSet h_cheap `S.union` resid_xs) entered_resid_step
        resid_xs' = fvs' `S.union` newly_resid
        resid_kfs' = IS.fromList [i | (i, kf) <- named_k, Update (annee -> x') <- [kf], x' `S.member` resid_xs']

-- Note [Better fixed points of Entered information]
--
-- Consider this example:
--
--   ex_used_once |-> if unk then False else True
--   ex_uses_ex |-> if ex_used_once then True else False
--   one |-> f ex_uses_ex
--   two |-> g ex_uses_ex
--   (one, two)
--
-- If we just optimistically inline all heap bindings in the first step, we get:
--
--   one |-> < ex_used_once |-> if unk then False else True,
--             ex_uses_ex |-> if ex_used_once then True else False
--           | f ex_uses_ex | >
--   two |-> < ex_used_once |-> if unk then False else True,
--             ex_uses_ex |-> if ex_used_once then True else False
--           | g ex_uses_ex | >
--   (one, two)
--
-- If we now compute the Entered information based on this proposal, we mark both
-- ex_used_once and ex_uses_ex as Many but non-cheap and hence force them to be residualised.
-- However, this is too pessimistic because once we residualise ex_uses_ex there is only one
-- occurrenc of ex_used_once.
--
-- The right thing to do is to only mark as residualised due to expense concrens those bindings
-- that would have been marked as expensive *regardless of the choice of any other binding's expense*.
-- So ex_used_once should not be marked as residualised because we only inlined it due to it being
-- a free variable of something which transitioned from inlineable to non-inlineable.
--
--
-- The solution works as follows:
--  * When inlining the heap into brackets, we record for each heap binding that we inline all the
--    "paths" through which they got inlined. If something was a direct FV of one of the brackets,
--    that will lead to a path of []. If something was a FV of a binding x that was itself a FV
--    of the bracket then the path will be [x].
--  * When deciding what to residualise for work-duplication reasons, we only force residualisation
--    for bindings that are BOTH:
--     a) Non-cheap and non-linear
--     b) Inlined through *any* path where each of the bindings on that path is certainly not
--        going to be residualised *this* time around the fixed point when it *wasn't last time*
--
--    This last condition ensures that we do not mark expensive bindings that are only *temporarily*
--    non-linear as residualised. Only bindings that actually have non-linearity arising from some
--    binding that is use that is not going to be fiddled with by future residualisations is permitted.
--    
--    In particular, this prevents ex_used_once from being marked Many even though the agressive inlining
--    outlined above causes it to be temporarily used non-linearly. Instead we delay until ex_uses_ex is
--    residualised and then see the truth -- ex_used_once is actually linear and can be inlined safely.

-- | Used to record which chain of inlinings caused some variable to be inlined
type Path = [Out Var]

-- | The paths through a bracket demands particular free variables
type FreeVarPaths = M.Map (Out Var) [Path]

-- We are going to use this helper function to inline any eligible inlinings to produce the expressions for driving.
-- Returns (along with the augmented state) the names of those bindings in the input PureHeap that could have been inlined
-- but were not due to generalisation.
transitiveInline :: Deeds -> PureHeap -> (Entered, State) -> (Deeds, FreeVarPaths, EnteredEnv, State)
transitiveInline deeds h_inlineable (ent, (Heap h ids, k, in_e))
    = -- (if not (S.null not_inlined_vs') then traceRender ("transitiveInline: generalise", not_inlined_vs') else id) $
      (deeds', paths, mkEnteredEnv ent (M.keysSet h' S.\\ M.keysSet h), (Heap h' ids, k, in_e))
  where
    (deeds', paths, h') = go 0 deeds (h_inlineable `M.union` h) M.empty (setToMap [[]] (stateFreeVars (Heap M.empty ids, k, in_e)))
    
    go :: Int -> Deeds -> PureHeap -> PureHeap -> M.Map (Out Var) [Path] -> (Deeds, M.Map (Out Var) [Path], PureHeap)
    go n deeds h_inlineable h_output fvs_paths = -- traceRender ("go", n, M.keysSet h_inlineable, M.keysSet h_output, fvs) $
                                                 if M.null h_inline then (deeds', fvs_paths, h_output)
                                                                    else go (n + 1) deeds' (h_inlineable' `M.union` h_not_inlined) (h_output `M.union` h_inline) fvs'
      where -- Generalisation heuristic: only inline those members of the heap which do not cause us to blow the whistle
            --
            -- NB: we rely here on the fact that our caller will still be able to fill in bindings for stuff from h_inlineable
            -- even if we choose not to inline it into the State, and that such bindings will not be evaluated until they are
            -- actually demanded (or we could get work duplication by inlining into only *some* Once contexts).
            --
            -- NB: we rely here on the fact that the original h contains "optional" bindings in the sense that they are shadowed
            -- by something bound above.
            consider_inlining x' in_e@(_, e) (deeds, h_inline, h_not_inlined) = case claimDeed deeds (annedTag e) of
                Nothing    -> traceRender ("transitiveInline: deed claim failure", x') (deeds,                  h_inline, M.insert x' in_e h_not_inlined)
                Just deeds ->                                                          (deeds, M.insert x' in_e h_inline,                  h_not_inlined)
            (deeds', h_inline, h_not_inlined) = M.foldWithKey consider_inlining (deeds, M.empty, M.empty) h_inline_candidates
            (h_inline_candidates, h_inlineable') = M.partitionWithKey (\x' _ -> x' `M.member` fvs_paths) h_inlineable
            fvs' = M.foldWithKey (\x' in_e fvs_paths -> M.unionWith (++) fvs_paths (setToMap (map (x' :) (fromJust (M.lookup x' fvs_paths))) (inFreeVars annedTermFreeVars in_e))) fvs_paths h_inline


-- TODO: replace with a genuine evaluator. However, think VERY hard about the termination implications of this!
-- I think we can only do it when the splitter is being invoked by a non-whistling invocation of sc.
cheapifyHeap :: (Deeds, Heap) -> (Deeds, Heap)
cheapifyHeap deedsheap | not sPLITTER_CHEAPIFICATION = deedsheap
cheapifyHeap (deeds, Heap h (splitIdSupply -> (ids, ids'))) = (deeds', Heap (M.fromList floats `M.union` h') ids')
  where
    ((deeds', _, floats), h') = M.mapAccum (\(deeds, ids, floats0) in_e -> case cheapify deeds ids in_e of (deeds, ids, floats1, in_e') -> ((deeds, ids, floats0 ++ floats1), in_e')) (deeds, ids, []) h
    
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
              M.Map (Out Var) (Tagged (Bracketed (Entered, IdSupply -> State))),
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
                    M.Map (Out Var) (Tagged (Bracketed (Entered, IdSupply -> State))),
                    Bracketed (Entered, IdSupply -> State))
splitStackFrame ids kf scruts bracketed_hole
  | Update x' <- kf = splitUpdate scruts x' bracketed_hole
  | otherwise = ([], M.empty, case kf of
    Apply (annee -> x2') -> zipBracketeds (\[e] -> e `app` x2') (\[fvs] -> S.insert x2' fvs) (\[fvs] -> fvs) (\_ -> Nothing) [bracketed_hole]
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    -- (if not (null k_not_inlined) then traceRender ("splitStack: generalise", k_not_inlined) else id) $
                                                    zipBracketeds (\(e_hole:es_alts) -> case_ e_hole (alt_cons' `zip` es_alts)) (\(fvs_hole:fvs_alts) -> fvs_hole `S.union` S.unions (zipWith (S.\\) fvs_alts alt_bvss)) (\(vs_hole:vs_alts) -> vs_hole `S.union` S.unions (zipWith (S.\\) vs_alts alt_bvss)) (\(_tails_hole:tailss_alts) -> liftM concat (sequence tailss_alts)) (bracketed_hole : bracketed_alts)
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
            alt_hs = zipWith3 (\alt_rn alt_con alt_tg -> M.fromList $ do { Just scrut_v <- [altConToValue alt_con]; scrut <- scruts; return (scrut, (alt_rn, annedTerm alt_tg (Value scrut_v))) }) alt_rns alt_cons (map annedTag alt_es)
            alt_bvss = map (\alt_con' -> fst $ altConOpenFreeVars alt_con' (S.empty, S.empty)) alt_cons'
            bracketed_alts = zipWith (\alt_h alt_in_e -> oneBracketed (Once ctxt_id, \ids -> (Heap alt_h ids, [], alt_in_e))) alt_hs alt_in_es
    PrimApply pop in_vs in_es -> zipBracketeds (primOp pop) S.unions S.unions (\_ -> Nothing) (bracketed_vs ++ bracketed_hole : bracketed_es)
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

splitUpdate :: [Out Var] -> Out (Anned Var) -> Bracketed (Entered, IdSupply -> State)
            -> ([Out Var], M.Map (Out Var) (Tagged (Bracketed (Entered, IdSupply -> State))), Bracketed (Entered, IdSupply -> State))
splitUpdate scruts x' bracketed_hole = (annee x' : scruts, M.singleton (annee x') (Tagged (annedTag x') bracketed_hole), noneBracketed (var (annee x')) (S.singleton (annee x'))) -- FIXME: sort of crappy source of tags for the bracketed info

splitValue :: IdSupply -> In AnnedValue -> Bracketed (Entered, IdSupply -> State)
splitValue ids (rn, Lambda x e) = zipBracketeds (\[e'] -> lambda x' e') (\[fvs'] -> fvs') (\[fvs'] -> S.delete x' fvs') (\_ -> Nothing) [oneBracketed (Many, \ids -> (Heap M.empty ids, [], (rn', e)))]
  where (_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v             = noneBracketed (value v') (inFreeVars annedValueFreeVars' in_v)
  where v' = detagAnnedValue' $ renameIn renameAnnedValue' ids in_v

splitQA :: IdSupply -> In QA -> Bracketed (Entered, IdSupply -> State)
splitQA _   (rn, Question x) = noneBracketed (var x') (S.singleton x')
  where x' = rename rn x
splitQA ids (rn, Answer v)   = splitValue ids (rn, v)
