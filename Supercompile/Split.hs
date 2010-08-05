{-# LANGUAGE ViewPatterns, TupleSections, DeriveFunctor, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (Statics, MonadStatics(..), split) where

--import Supercompile.Residualise

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate (step)
import Evaluator.FreeVars
import Evaluator.Syntax

import Size.Deeds

import Algebra.PartialOrd
import Algebra.Lattice
import Name
import Renaming
import StaticFlags
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import qualified Data.Map as M
import qualified Data.Set as S


type Statics = FreeVars

class Monad m => MonadStatics m where
    withStatics :: FreeVars -> m a -> m (Out [(Var, FVedTerm)], a)


--
-- == Gathering entry information for the splitter ==
--

data Entered = Once (Maybe Id) -- ^ The Id is a context identifier: if a binding is Entered twice from the same context it's really a single Entrance. Nothing signifies the residual context (i.e. there is no associated float)
             | Many Bool       -- ^ The Bool records whether any of those Many occurrences are in the residual
             deriving (Eq, Show)

instance Pretty Entered where
    pPrint = text . show

instance JoinSemiLattice Entered where
    join = plusEntered

isOnce :: Entered -> Bool
isOnce (Once _) = True
isOnce _ = False

enteredInResidual :: Entered -> Bool
enteredInResidual (Once mb_id) = isNothing mb_id
enteredInResidual (Many resid) = resid

plusEntered :: Entered -> Entered -> Entered
plusEntered (Once mb_id1) (Once mb_id2)
  | mb_id1 == mb_id2 = Once mb_id1
  | otherwise        = {- traceRender ("Once promotion", mb_id1, mb_id2) $ -} Many (isNothing mb_id1 || isNothing mb_id2)
plusEntered e1 e2 = Many (enteredInResidual e1 || enteredInResidual e2)


type EnteredEnv = M.Map (Out Var) Entered

mkEnteredEnv :: Entered -> FreeVars -> EnteredEnv
mkEnteredEnv = setToMap


--
-- == The splitter ==
--


split :: MonadStatics m
      => ((Deeds, State) -> m (Deeds, Out FVedTerm))
      -> (Deeds, State)
      -> m (Deeds, Out FVedTerm)
split opt (deeds, s) = uncurry3 (optimiseSplit opt) (splitt (simplify (deeds, s)))

-- Non-expansive simplification that we can safely do just before splitting to make the splitter a bit simpler
data QA = Question Var
        | Answer   (ValueF Anned)

simplify :: (Deeds, State) -> (Deeds, (Heap, Stack, In (Anned QA)))
simplify (deeds, s) = expectHead "simplify" [(deeds, res) | (deeds, s) <- (deeds, s) : unfoldr (\(deeds, s) -> fmap (\x -> (x, x)) (step (const id) S.empty (deeds, s))) (deeds, s), Just res <- [stop s]]
  where
    stop (h, k, (rn, Comp (Tagged tg (FVed fvs (Var x)))))   = Just (h, k, (rn, Comp (Tagged tg (FVed fvs (Question x)))))
    stop (h, k, (rn, Comp (Tagged tg (FVed fvs (Value v))))) = Just (h, k, (rn, Comp (Tagged tg (FVed fvs (Answer v)))))
    stop _ = Nothing

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
    transfer :: [FreeVars] -> FreeVars,        -- Strips any variables bound by the residual out of the hole FVs
    fillers :: [a]                             -- Hole-fillers themselves. Usually State
  } deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Accumulatable Bracketed where
    mapAccumTM f acc b = liftM (\(acc', fillers') -> (acc', b { fillers = fillers' })) $ mapAccumTM f acc (fillers b)

noneBracketed :: Out FVedTerm -> FreeVars -> Bracketed a
noneBracketed a b = Bracketed {
    rebuild  = \[] -> a,
    extraFvs = b,
    transfer = \[] -> S.empty,
    fillers  = []
  }

oneBracketed :: a -> Bracketed a
oneBracketed x = Bracketed {
    rebuild  = \[e] -> e,
    extraFvs = S.empty,
    transfer = \[fvs] -> fvs,
    fillers  = [x]
  }

zipBracketeds :: ([Out FVedTerm] -> Out FVedTerm)
              -> ([FreeVars] -> FreeVars)
              -> ([FreeVars] -> FreeVars)
              -> [Bracketed a]
              -> Bracketed a
zipBracketeds a b c bracketeds = Bracketed {
      rebuild  = \(splitManyBy xss -> ess') -> a (zipWith rebuild bracketeds ess'),
      extraFvs = b (map extraFvs bracketeds),
      transfer = \(splitManyBy xss -> fvss) -> c (zipWith transfer bracketeds fvss),
      fillers  = concat xss
    }
  where xss = map fillers bracketeds

bracketedFreeVars :: (a -> FreeVars) -> Bracketed a -> FreeVars
bracketedFreeVars fvs bracketed = extraFvs bracketed `S.union` transfer bracketed (map fvs (fillers bracketed))


optimiseMany :: Monad m
             => ((Deeds, a) -> m (Deeds, Out FVedTerm))
             -> (Deeds, [a])
             -> m (Deeds, [Out FVedTerm])
optimiseMany opt (deeds, xs) = mapAccumLM (\deeds s -> opt (deeds, s) >>= \(deeds, e') -> return (deeds, e')) deeds xs

optimiseBracketed :: MonadStatics m
                  => ((Deeds, State) -> m (Deeds, Out FVedTerm))
                  -> (Deeds, Bracketed State)
                  -> m (Deeds, Out FVedTerm)
optimiseBracketed opt (deeds, b) = do
    (deeds', es') <- optimiseMany opt (deeds, fillers b)
    return (deeds', rebuild b es')

optimiseSplit :: MonadStatics m
              => ((Deeds, State) -> m (Deeds, Out FVedTerm))
              -> Deeds
              -> M.Map (Out Var) (Bracketed State)
              -> Bracketed State
              -> m (Deeds, Out FVedTerm)
optimiseSplit opt deeds bracketeds_heap bracketed_focus = do
    -- 1) Recursively drive the focus itself
    let statics = M.keysSet bracketeds_heap
    (hes, (deeds, e_focus)) <- withStatics statics $ optimiseBracketed opt (deeds, bracketed_focus)
    
    -- 2) We now need to think about how we are going to residualise the letrec. In fact, we need to loop adding
    -- stuff to the letrec because it might be the case that:
    --  * One of the hes from above refers to some heap binding that is not referred to by the let body
    --  * So after we do withStatics above we need to drive some element of the bracketeds_heap
    --  * And after driving that we find in our new hes a new h function referring to a new free variable
    --    that refers to some binding that is as yet unbound...
    (deeds, bracketeds_heap, xes, _fvs) <- go hes statics deeds bracketeds_heap [] (fvedTermFreeVars e_focus)
    
    -- 3) Combine the residualised let bindings with the let body
    return (foldl' (\deeds b -> foldl' releaseStateDeed deeds (fillers b)) deeds (M.elems bracketeds_heap),
            letRecSmart xes e_focus)
  where
    -- TODO: clean up this incomprehensible loop
    -- TODO: investigate the possibility of just fusing in the optimiseLetBinds loop with this one
    go hes statics deeds bracketeds_heap xes fvs = do
        let statics' = statics `S.union` S.fromList (map fst hes) -- NB: the statics already include all the binders from bracketeds_heap, so no need to add xes stuff
        (hes', (deeds, bracketeds_heap, fvs, xes')) <- withStatics statics' $ optimiseLetBinds opt deeds bracketeds_heap (fvs `S.union` S.unions (map (fvedTermFreeVars . snd) hes)) -- TODO: no need to get FVs in this way (they are in Promise)
        (if null hes' then (\a b c d -> return (a,b,c,d)) else go hes' statics') deeds bracketeds_heap (xes ++ hes ++ xes') fvs


-- We only want to drive (and residualise) as much as we actually refer to. This loop does this: it starts
-- by residualising the free variables of the focus residualisation (or whatever is in the let body),
-- and then transitively inlines any bindings whose corresponding binders become free.
optimiseLetBinds :: MonadStatics m
                 => ((Deeds, State) -> m (Deeds, Out FVedTerm))
                 -> Deeds
                 -> M.Map (Out Var) (Bracketed State)
                 -> FreeVars
                 -> m (Deeds, M.Map (Out Var) (Bracketed State), FreeVars, Out [(Var, FVedTerm)])
optimiseLetBinds opt deeds bracketeds_heap fvs' = traceRender ("optimiseLetBinds", M.keysSet bracketeds_heap, fvs') $
                                                  go deeds bracketeds_heap [] fvs'
  where
    go deeds bracketeds_heap_not_resid xes_resid resid_fvs
      | M.null h_resid = -- traceRenderM ("go", resid_fvs, resid_bvs, (M.map (residualiseBracketed (residualiseState . first3 (flip Heap prettyIdSupply))) bracketeds_heap)) $
                         return (deeds, bracketeds_heap_not_resid, resid_fvs, xes_resid)
      | otherwise = {- traceRender ("optimiseSplit", xs_resid') $ -} do
        -- Recursively drive the new residuals arising from the need to bind the resid_fvs
        (deeds, es_resid') <- optimiseMany (optimiseBracketed opt) (deeds, bracks_resid)
        let extra_resid_fvs' = S.unions (map fvedTermFreeVars es_resid')
        -- Recurse, because we might now need to residualise and drive even more stuff (as we have added some more FVs and BVs)
        go deeds bracketeds_heap_not_resid'
                 (xes_resid ++ zip xs_resid' es_resid')
                 (resid_fvs `S.union` extra_resid_fvs')
      where
        -- When assembling the final list of things to drive, ensure that we exclude already-driven things
        (h_resid, bracketeds_heap_not_resid') = M.partitionWithKey (\x _br -> x `S.member` resid_fvs) bracketeds_heap_not_resid
        (xs_resid', bracks_resid) = unzip $ M.toList h_resid


splitt :: (Deeds, (Heap, Stack, In (Anned QA))) -- ^ The thing to split, and the Deeds we have available to do it
       -> (Deeds,                               -- ^ The Deeds still available after splitting
           M.Map (Out Var) (Bracketed State),   -- ^ The residual "let" bindings
           Bracketed State)                     -- ^ The residual "let" body
splitt (old_deeds, (cheapifyHeap . (old_deeds,) -> (deeds, Heap h (splitIdSupply -> (ids_brack, splitIdSupply -> (ids1, ids2)))), k, in_qa))
    = -- traceRender ("splitt", residualiseHeap (Heap h ids_brack) (\ids -> residualiseStack ids k (case tagee qa of Question x' -> var x'; Answer in_v -> value $ detagTaggedValue $ renameIn renameTaggedValue ids in_v))) $
      snd $ split_step resid_xs -- TODO: eliminate redundant recomputation here?
  where
    -- Note that as an optimisation, optimiseSplit will only actually creates those residual bindings if the
    -- corresponding variables are free *after driving*. Of course, we have no way of knowing which bindings
    -- will get this treatment here, so just treat resid_xs as being exactly the set of residualised stuff.
    resid_xs = lfp (fst . split_step)
    
    -- Simultaneously computes the next fixed-point step and some artifacts computed along the way,
    -- which happen to correspond to exactly what I need to return from splitt.
    split_step resid_xs = -- traceRender ("split_step", resid_xs, fvs', resid_xs') $
                          (resid_xs', (deeds2, bracketeds_heap', bracketed_focus'))
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
          = (\(a, b, c) -> (a, M.map fill_ids b, fill_ids c)) $
            splitStack ids2 resid_xs deeds (case annee (snd in_qa) of Question x -> [rename (fst in_qa) x]; Answer _ -> []) k (splitQA ids1 in_qa)
        
        -- 2) Build a splitting for those elements of the heap we propose to residualise in resid_xs
        (h_residualised, h_not_residualised) = M.partitionWithKey (\x' _ -> x' `S.member` resid_xs) h
        bracketeds_nonupdated = M.mapWithKey (\x' in_e -> oneBracketed (Once (Just (fromJust (name_id x'))), (Heap M.empty ids_brack, [], in_e))) h_residualised
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
        h_inlineable = h_not_residualised `M.union` h_cheap
        
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
        (deeds1, fvs_paths_focus', entered_focus, bracketed_focus') =             inlineBracketHeap deeds0 bracketed_focus
        (deeds2, fvs_paths_heap',  entered_heap,  bracketeds_heap') = inlineHeapT inlineBracketHeap deeds1 bracketeds_heap

        -- 4) Construct the next element of the fixed point process:
        --  a) We should also residualise bindings that occur as free variables of any of the
        --     elements of the (post-inlining) residualised heap or focus. As a side effect, this will pick up
        --     any variables that should be residualised due to generalisation
        --  b) Lastly, we should residualise non-cheap bindings that got Entered more than once in the proposal
        --     to make the splitter more agressive (see Note [Better fixed points of Entered information]), I only
        --     do this for bindings that were actually direct free variables of the original term.
        fvs' = bracketedFreeVars stateFreeVars bracketed_focus' `S.union` S.unions [bracketedFreeVars stateFreeVars bracketed' | (_, bracketed') <- M.toList bracketeds_heap']
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


splitStack :: IdSupply
           -> S.Set Var -- ^ Those variables that must be bound now, and cannot have their update frames pushed down
           -> Deeds
           -> [Out Var]
           -> Stack
           -> Bracketed (Entered, IdSupply -> State)
           -> (Deeds,
               M.Map (Out Var) (Bracketed (Entered, IdSupply -> State)),
               Bracketed (Entered, IdSupply -> State))
splitStack _   _                 deeds _      []     bracketed_hole = (deeds, M.empty, bracketed_hole)
splitStack ids must_bind_updates deeds scruts (kf:k) bracketed_hole = case kf of
    Apply (annee -> x2') -> splitStack ids must_bind_updates deeds [] k (zipBracketeds (\[e] -> e `app` x2') (\[fvs] -> S.insert x2' fvs) (\[fvs] -> fvs) [bracketed_hole])
    -- NB: case scrutinisation is special! Instead of kontinuing directly with k, we are going to inline
    -- *as much of entire remaining evaluation context as we can* into each case branch. Scary, eh?
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    (if not (null k_not_inlined) then traceRender ("splitStack: generalise", k_not_inlined) else id) $
                                                    splitStack ids' must_bind_updates deeds' [] (k_not_inlined ++ k_remaining) (zipBracketeds (\(e_hole:es_alts) -> case_ e_hole (alt_cons' `zip` es_alts)) (\(fvs_hole:fvs_alts) -> fvs_hole `S.union` S.unions (zipWith (S.\\) fvs_alts alt_bvss)) (\(vs_hole:vs_alts) -> vs_hole `S.union` S.unions (zipWith (S.\\) vs_alts alt_bvss)) (bracketed_hole : bracketed_alts))
      where -- 0) Manufacture context identifier
            (ids', state_ids) = splitIdSupply ids
            ctxt_id = idFromSupply state_ids
            
            -- (Once (Just ctxt_id))
        
            -- 1) Split the continuation eligible for inlining into two parts: that part which can be pushed into
            -- the case branch, and that part which could have been except that we need to refer to a variable it binds
            -- in the residualised part of the term we create
            (k_inlineable_candidates, k_remaining) = span (`does_not_bind_any_of` must_bind_updates) k
            does_not_bind_any_of (Update x') fvs = annee x' `S.notMember` fvs
            does_not_bind_any_of _ _ = True
        
            -- 2) Construct the floats for each case alternative by pushing in that continuation
            (_alt_ids', alt_rns, alt_cons') = unzip3 $ map (renameAltCon ids' rn) alt_cons
            -- Bind something to the case scrutinee (if possible). This means that:
            --  let y = (\z -> case z of C -> ...) unk
            --  in y
            -- ===>
            --  case x of C -> let unk = C; z = C in ...
            alt_in_es = alt_rns `zip` alt_es
            alt_hs = zipWith3 (\alt_rn alt_con alt_tg -> M.fromList $ do { Just scrut_v <- [altConToValue alt_con]; scrut <- scruts; return (scrut, (alt_rn, annedTerm alt_tg (Value scrut_v))) }) alt_rns alt_cons (map annedTag alt_es)
            alt_bvss = map (\alt_con' -> fst $ altConOpenFreeVars alt_con' (S.empty, S.empty)) alt_cons'
            (deeds', k_not_inlined, bracketed_alts) = third3 (map oneBracketed) $ go deeds k_inlineable_candidates (zipWith (\alt_h alt_in_e -> (Once (Just ctxt_id), \ids -> (Heap alt_h ids, [], alt_in_e))) alt_hs alt_in_es)
              where
                branch_factor = length alt_cons
                
                -- Inline parts of the evaluation context into each branch only if we can get that many deeds for duplication
                go deeds []     states = (deeds, [], states)
                go deeds (kf:k) states = case foldM (\deeds tag -> claimDeeds deeds tag (branch_factor - 1)) deeds (stackFrameTags kf) of -- NB: subtract one because one occurrence is already "paid for". It is OK if the result is negative (i.e. branch_factor 0)!
                    Nothing    -> traceRender ("splitStack: deed claim failure", length k) (deeds, kf:k, states)
                    Just deeds -> go deeds k (map (\(ent, f) -> (ent, second3 (++ [kf]) . f)) states)
    PrimApply pop in_vs in_es -> splitStack ids' must_bind_updates deeds [] k (zipBracketeds (primOp pop) S.unions S.unions (bracketed_vs ++ bracketed_hole : bracketed_es))
      where -- 0) Manufacture context identifier
            (ids', state_idss) = accumL splitIdSupply ids (length in_es)
            ctxt_ids = map idFromSupply state_idss
            
            -- 1) Split every value and expression remaining apart
            bracketed_vs = map (splitValue ids' . fmap annee) in_vs
            bracketed_es  = zipWith (\ctxt_id in_e -> oneBracketed (Once (Just ctxt_id), \ids -> (Heap M.empty ids, [], in_e))) ctxt_ids in_es
    Update (annee -> x') -> second3 (M.insert x' bracketed_hole) $ splitStack ids must_bind_updates deeds (x' : scruts) k (noneBracketed (var x') (S.singleton x'))
  where
    altConToValue :: AltCon -> Maybe (ValueF ann)
    altConToValue (DataAlt dc xs) = Just $ Data dc xs
    altConToValue (LiteralAlt l)  = Just $ Literal l
    altConToValue (DefaultAlt _)  = Nothing

splitValue :: IdSupply -> In AnnedValue -> Bracketed (Entered, IdSupply -> State)
splitValue ids (rn, Lambda x e) = zipBracketeds (\[e'] -> lambda x' e') (\[fvs'] -> fvs') (\[fvs'] -> S.delete x' fvs') [oneBracketed (Many False, \ids -> (Heap M.empty ids, [], (rn', e)))]
  where (_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v                  = noneBracketed (value v') (inFreeVars annedValueFreeVars' in_v)
  where v' = detagAnnedValue' $ renameIn renameAnnedValue' ids in_v

splitQA :: IdSupply -> In (Anned QA) -> Bracketed (Entered, IdSupply -> State)
splitQA _   (rn, annee -> Question x) = noneBracketed (var x') (S.singleton x')
  where x' = rename rn x
splitQA ids (rn, annee -> Answer v) = splitValue ids (rn, v)
