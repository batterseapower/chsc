{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (Statics, MonadStatics(..), split) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate (step)
import Evaluator.FreeVars
import Evaluator.Syntax

import Size.Deeds

import Name
import Renaming
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import qualified Data.Map as M
import qualified Data.Set as S


type Statics = FreeVars

class Monad m => MonadStatics m where
    withStatics :: FreeVars -> m a -> m ([(Out Var, Out Term)], a)


--
-- == Gathering entry information for the splitter ==
--

data Entered = Once (Maybe Id) -- ^ The Id is a context identifier: if a binding is Entered twice from the same context it's really a single Entrance. Nothing signifies the residual context (i.e. there is no associated float)
             | Many Bool       -- ^ The Bool records whether any of those Many occurrences are in the residual
             deriving (Eq, Show)

instance Pretty Entered where
    pPrint = text . show

isOnce :: Entered -> Bool
isOnce (Once _) = True
isOnce _ = False

enteredInResidual :: Entered -> Bool
enteredInResidual (Once mb_id) = isNothing mb_id
enteredInResidual (Many resid) = resid

plusEntered :: Entered -> Entered -> Entered
plusEntered (Once mb_id1) (Once mb_id2)
  | mb_id1 == mb_id2 = Once mb_id1
  | otherwise        = {- traceRender ("Once promotion", mb_id1, mb_id2) -} (Many (isNothing mb_id1 || isNothing mb_id2))
plusEntered e1 e2 = Many (enteredInResidual e1 || enteredInResidual e2)

type EnteredEnv = M.Map (Out Var) Entered

emptyEnteredEnv :: EnteredEnv
emptyEnteredEnv = M.empty

mkEnteredEnv :: Entered -> FreeVars -> EnteredEnv
mkEnteredEnv ent = M.fromList . map (, ent) . S.toList

plusEnteredEnv :: EnteredEnv -> EnteredEnv -> EnteredEnv
entenv1 `plusEnteredEnv` entenv2 = M.unionWith plusEntered entenv1 entenv2

plusEnteredEnvs :: [EnteredEnv] -> EnteredEnv
plusEnteredEnvs = foldr plusEnteredEnv emptyEnteredEnv


--
-- == The splitter ==
--


split :: MonadStatics m
      => ((Deeds, State) -> m (Deeds, FreeVars, Out Term))
      -> (Deeds, State)
      -> m (Deeds, FreeVars, Out Term)
split opt (simplify -> (deeds, (Heap h (splitIdSupply -> (ids1, ids2)), k, qa))) = uncurry3 (optimiseSplit opt) (split' deeds (Heap h ids1) k (case tagee qa of Question x' -> [x']; Answer _ -> []) (splitQA ids2 qa))

-- Non-expansive simplification that we can safely do just before splitting to make the splitter a bit simpler
data QA = Question (Out Var)
        | Answer   (In TaggedValue)

simplify :: (Deeds, State) -> (Deeds, (Heap, Stack, Tagged QA))
simplify (deeds, s) = expectHead "simplify" [(deeds, res) | (deeds, s) <- (deeds, s) : unfoldr (\(deeds, s) -> fmap (\x -> (x, x)) (step (deeds, s))) (deeds, s), Just res <- [stop s]]
  where
    stop (h, k, (rn, Tagged tg (Var x)))   = Just (h, k, Tagged tg (Question (rename rn x)))
    stop (h, k, (rn, Tagged tg (Value v))) = Just (h, k, Tagged tg (Answer (rn, v)))
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
    rebuild :: [Out Term] -> Out Term,  -- Rebuild the full output term given outputs to plug into each hole
    extra_fvs :: FreeVars,              -- Maximum free variables added by the residual wrapped around the holes
    transfer :: [FreeVars] -> FreeVars, -- Strips any variables bound by the residual out of the hole FVs
    fillers :: [a]                      -- Hole-fillers themselves. Usually State
  } deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Accumulatable Bracketed where
    mapAccumTM f acc b = liftM (\(acc', fillers') -> (acc', b { fillers = fillers' })) $ mapAccumTM f acc (fillers b)

optimiseMany :: Monad m
             => ((Deeds, a) -> m (Deeds, FreeVars, Out Term))
             -> (Deeds, [a])
             -> m (Deeds, [FreeVars], [Out Term])
optimiseMany opt (deeds, xs) = liftM (\(deeds', unzip -> (fvs', es')) -> (deeds', fvs', es')) $ mapAccumLM (\deeds s -> opt (deeds, s) >>= \(deeds, fvs, e') -> return (deeds, (fvs, e'))) deeds xs

optimiseBracketed :: MonadStatics m
                  => ((Deeds, State) -> m (Deeds, FreeVars, Out Term))
                  -> (Deeds, Bracketed State)
                  -> m (Deeds, FreeVars, Out Term)
optimiseBracketed opt (deeds, b) = do
    (deeds', fvs', es') <- optimiseMany opt (deeds, fillers b)
    return (deeds', extra_fvs b `S.union` transfer b fvs', rebuild b es')

-- We are going to use this helper function to inline any eligible inlinings to produce the expressions for driving
-- Returns (along with the augmented state) the names of those bindings in the input PureHeap that could have been inlined
-- but were not due to generalisation.
transitiveInline :: Deeds -> PureHeap -> State -> (Deeds, FreeVars, State)
transitiveInline deeds h_inlineable (Heap h ids, k, in_e) = (if not (S.null not_inlined_vs') then traceRender ("transitiveInline: generalise", not_inlined_vs') else id) $
                                                            (deeds', not_inlined_vs', (Heap h' ids, k, in_e))
  where
    (deeds', not_inlined_vs', h') = go 0 deeds (h_inlineable `M.union` h) M.empty (stateFreeVars (Heap M.empty ids, k, in_e))
    
    go :: Int -> Deeds -> PureHeap -> PureHeap -> FreeVars -> (Deeds, FreeVars, PureHeap)
    go n deeds h_inlineable h_output fvs = -- traceRender ("go", n, M.keysSet h_inlineable, M.keysSet h_output, fvs) $
                                           if M.null h_inline then (deeds', M.keysSet h_not_inlined, h_output)
                                                              else go (n + 1) deeds' (h_inlineable' `M.union` h_not_inlined) (h_output `M.union` h_inline) fvs'
      where -- Generalisation heuristic: only inline those members of the heap which do not cause us to blow the whistle
            -- NB: we rely here on the fact that our caller will still be able to fill in bindings for stuff from h_inlineable
            -- even if we choose not to inline it into the State, and that such bindings will not be evaluated until they are
            -- actually demanded (or we could get work duplication by inlining into only *some* Once contexts).
            consider_inlining x' in_e@(_, e) (deeds, h_inline, h_not_inlined) = case claimDeed deeds (tag e) of
                Nothing    -> traceRender ("transitiveInline: deed claim failure", x') (deeds,                  h_inline, M.insert x' in_e h_not_inlined)
                Just deeds ->                                                          (deeds, M.insert x' in_e h_inline,                  h_not_inlined)
            (deeds', h_inline, h_not_inlined) = M.foldWithKey consider_inlining (deeds, M.empty, M.empty) h_inline_candidates
            (h_inline_candidates, h_inlineable') = M.partitionWithKey (\x' _ -> x' `S.member` fvs) h_inlineable
            fvs' = M.fold (\in_e fvs -> fvs `S.union` inFreeVars taggedTermFreeVars in_e) fvs h_inline

optimiseSplit :: MonadStatics m
              => ((Deeds, State) -> m (Deeds, FreeVars, Out Term))
              -> Deeds
              -> M.Map (Out Var) (Bracketed State)
              -> Bracketed State
              -> m (Deeds, FreeVars, Out Term)
optimiseSplit opt deeds floats_h floats_compulsory = do
    -- 1) Recursively drive the compulsory floats
    (deeds, fvs_compulsory', e_compulsory') <- optimiseBracketed opt (deeds, floats_compulsory)
    
    -- 2) We now need to think about how we are going to residualise the letrec. We only want to drive (and residualise) as
    --    much as we actually refer to. This loop does this: it starts by residualising the free variables of the compulsory
    --    residualisation, and then transitively inlines any bindings whose corresponding binders become free.
    let residualise deeds xes_resid resid_bvs resid_fvs
          | M.null h_resid = -- traceRenderM ("residualise", resid_fvs, resid_bvs, (M.map (residualiseBracketed (residualiseState . first3 (flip Heap prettyIdSupply))) floats_h)) $
                             return (foldl' (\deeds b -> foldl' releaseStateDeed deeds (fillers b)) deeds (M.elems floats_not_resid), resid_fvs S.\\ resid_bvs, xes_resid)
          | otherwise = {- traceRender ("optimiseSplit", xs_resid') $ -} do
            -- Recursively drive the new residuals arising from the need to bind the resid_fvs
            (deeds, S.unions -> extra_resid_fvs', es_resid') <- optimiseMany (optimiseBracketed (\(deeds, s) -> liftM (\(hes', (deeds', vs', e')) -> (deeds', vs', letRec hes' e')) $ withStatics (M.keysSet floats_h `S.intersection` stateFreeVars s) $ opt (deeds, s))) (deeds, bracks_resid)
            -- Recurse, because we might now need to residualise and drive even more stuff (as we have added some more FVs and BVs)
            residualise deeds (xes_resid ++ zip xs_resid' es_resid')
                              (resid_bvs `S.union` M.keysSet h_resid)
                              (resid_fvs `S.union` extra_resid_fvs')
          where
            -- When assembling the final list of things to drive, ensure that we exclude already-driven things
            floats_not_resid = floats_h `exclude` resid_bvs
            h_resid = M.filterWithKey (\x _br -> x `S.member` resid_fvs) floats_not_resid
            (xs_resid', bracks_resid) = unzip $ M.toList h_resid

    (deeds, fvs', xes') <- residualise deeds [] S.empty fvs_compulsory'
    return (deeds, fvs', letRec xes' e_compulsory')

-- Whether the given variable was entered many times, with no context identifier information required
-- I'm using this abstraction to make explicit the fact that we don't pass context identifiers between
-- iterations of the splitter "go" loop. This is important because they are potentially unstable!
type EnteredManyEnv = M.Map (Out Var) Bool

toEnteredManyEnv :: EnteredEnv -> EnteredManyEnv
toEnteredManyEnv = M.map (not . isOnce)

split'
  :: Deeds
  -> Heap
  -> Stack
  -> [Out Var]
  -> (EnteredEnv, Bracketed State)
  -> (Deeds,
      M.Map (Out Var) (Bracketed State), -- FIXME: for best Deeds performance, should only contain stuff that genuinely might be residualised! Should have Deed for each entry.
      Bracketed State)
split' old_deeds old_h@((cheapifyHeap . (old_deeds,)) -> (deeds, Heap h (splitIdSupply -> (ids1, ids2)))) k scruts (entered_hole, bracketed_hole)
  = go S.empty (toEnteredManyEnv entered_hole)
  where
    go must_resid_k_xs entered_many
      | not (S.null gen_fvs) && traceRender ("split.go", gen_fvs, must_resid_k_xs, entered_many) False = undefined
      -- | traceRender ("split.release", M.keysSet h_strictly_inlined) False = undefined
      -- | traceRender ("split.go", entered, entered_k, xs_nonvalue_inlinings) False = undefined
      | entered_many == entered_many'
      , must_resid_k_xs == must_resid_k_xs'
      = -- (\res -> traceRender ("split'", entered_hole, "==>", entered_k, "==>", entered', must_resid_k_xs, [x' | Tagged _ (Update x') <- k], M.keysSet floats_k_bound) res) $
        (\res@(_, avail_h, _) -> traceRender ("split'", M.keysSet h_strictly_inlined, deeds, deeds0, deeds3, M.keysSet (case old_h of Heap h _ -> h), M.keysSet h, M.keysSet avail_h, M.keysSet h_inlineable, entered_many, entered') res) $
        (deeds3, brackets_h `M.union` brackets_k_bound, bracket_k')
      | otherwise = go must_resid_k_xs' entered_many'
      where
        -- Evaluation context splitting
        -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        
        -- Guess how to split up the evaluation context, based on residualising those update frames
        -- that bound any variables free the last time around the loop.
        -- NB: we add the FVs of the part of the heap that we *have* to residualise to the entered_hole
        -- information. This ensures that splitStack residualises the update frames for any of
        -- those FVs that it happens to bind, which is essential for correctness.
        (deeds0_unreleased, floats_k_bound, (entered_k, bracket_k)) = splitStack deeds ids1 scruts k (entered_hole `plusEnteredEnv` mkEnteredEnv (Once Nothing) must_resid_k_xs, bracketed_hole)
        
        -- Heap splitting
        -- ~~~~~~~~~~~~~~
        
        -- Guess which parts of the heap are safe for inlining based on the current Entered information
        (h_inlineable, entered', before_must_resid_k_xs') = splitPureHeap h entered_many entered_k
        
        -- NB: We must NOT take non-values that we have decided to inline and then bind them in the residual term. This does not
        -- usually happen because such things won't be free variables of the immediate output term, but with strict bindings the
        -- optimiser will be forced to residualise such bindings anyway.
        --
        -- Explicitly filter them out to be sure we don't spuriously recompute such bindings, BUT make sure to retain non-value
        -- bindings that are used Once by the *residual itself*:
        --
        -- NB: the below comment is outdated. It turns out we could fix the bug by just using must_resid_k_xs to communicate
        -- residualised stuff between iterations.
        -- NB: I used to do this, but no longer! The reason is that with generalisation we might choose not to inline some non-value,
        -- so it must be available to optimiseSplit if it turns out to be free.
        h_strictly_inlined    = M.filterWithKey (\x _ -> maybe True (not . enteredInResidual) (M.lookup x entered')) h_inlineable
        xs_nonvalue_inlinings = M.keysSet h_strictly_inlined -- $ M.filterWithKey (\x (_, e) -> maybe False (/= Once Nothing) (M.lookup x entered') && not (taggedTermIsCheap e)) h_inlineable
        
        -- Generalisation
        -- ~~~
        
        -- In order to make the Deeds-based stuff less conservative, my first action here is to release our claims to those deeds
        -- which we do *not* intend to create a residual let binding for here and now. This will let us always inline a heap-bound
        -- thing into *at least one* context (unless it really is referred to by the residual code).
        --
        -- The equivalent process is done for the stack in splitStack itself: we just subtract 1 from the number of deeds we need to
        -- claim when duplicating a stack frame.
        deeds0 = M.fold (\(_, e) deeds -> releaseDeedDeep deeds (tag e)) deeds0_unreleased h_strictly_inlined
        
        -- Generalising the final proposed floats may cause some bindings that we *thought* were going to be inlined to instead be
        -- residualised. We need to account for this in the Entered information (for work-duplication purposes), and in that we will
        -- also require any FVs of the new residualised things that are bound in the stack to residualise more frames.
        inlineHeapT :: Accumulatable t
                    => (Deeds -> a   -> (Deeds, FreeVars, b))
                    ->  Deeds -> t a -> (Deeds, FreeVars, t b)
        inlineHeapT f deeds b = (deeds', fvs', b')
          where ((deeds', fvs'), b') = mapAccumT (\(deeds, fvs) s -> case f deeds s of (deeds, fvs', s) -> ((deeds, fvs `S.union` fvs'), s)) (deeds, S.empty) b
        
        inlineBracketHeap :: Deeds -> Bracketed State -> (Deeds, FreeVars, Bracketed State)
        inlineBracketHeap = inlineHeapT (flip transitiveInline h_inlineable)
        
        (deeds1, gen_fvs_k',      bracket_k')       = inlineBracketHeap deeds0 bracket_k
        (deeds2, gen_fvs_h,       brackets_h)       = inlineHeapT (\deeds b -> inlineBracketHeap deeds (promoteToBracket b)) deeds1 (h              `exclude` xs_nonvalue_inlinings) -- NB: exclude *before* allowing
        (deeds3, gen_fvs_k_bound, brackets_k_bound) = inlineHeapT inlineBracketHeap                                          deeds2 (floats_k_bound `exclude` xs_nonvalue_inlinings) -- these guys to claim Deeds
        gen_fvs = gen_fvs_k' `S.union` gen_fvs_h `S.union` gen_fvs_k_bound
        
        -- FIXME: bit of a hack. At least needs some renaming. Basically just want to ensure that generalised variables are residualised,
        -- and that the resulting modifications to the Entered information takes effect.
        must_resid_k_xs' = gen_fvs `S.union` before_must_resid_k_xs'
                            `S.union` must_resid_k_xs -- NB: empirically, I have observed non-termination unless I make this set strictly growing (e.g. in TreeFlip-NoLiterals)
        
        entered_many' = toEnteredManyEnv entered'

    promoteToState :: In TaggedTerm -> State
    promoteToState in_e = (Heap M.empty ids2, [], in_e)

    promoteToBracket :: In TaggedTerm -> Bracketed State
    promoteToBracket in_e = Bracketed (\[e'] -> e') S.empty (\[fvs'] -> fvs') [promoteToState in_e]

splitPureHeap :: PureHeap -> M.Map Var Bool -> EnteredEnv -> (PureHeap, EnteredEnv, FreeVars)
splitPureHeap h was_entered_many entered_k = -- traceRender ("splitPureHeap", (residualisePureHeap prettyIdSupply h), (entered, entered_k), "=>", entered', must_resid_k_xs') $
                                             (h_inlineable, entered', must_resid_k_xs')
  where
    -- Linearity
    -- ~~~~~~~~~
    
    -- We have already gathered entry information from the Stack. Carry on, gathering
    -- it from the Heap as well. Assume Heap bindings are used as many times as they were used
    -- the last time we went around the loop.
    entered' = M.foldWithKey (\x' in_e entered' -> entered' `plusEnteredEnv` incorporate (fromJust $ name_id x') (M.lookup x' was_entered_many) in_e) entered_k h
    incorporate _ Nothing         _    = emptyEnteredEnv
    incorporate i (Just was_many) in_e = -- (\res -> traceRender ("incorporate", mb_id, ent, inFreeVars taggedTermFreeVars in_e) res) $
                                         mkEnteredEnv (if taggedTermIsCheap (snd in_e) && was_many then Many False else Once (Just i)) (inFreeVars taggedTermFreeVars in_e)
     -- Cheap things may be duplicated, so if they are used Many times so will their FVs be. Non-cheap things are either:
     --   a) Residualised immediately and so they enter their FVs at most Once
     --   b) Duplicated downwards, but used linearly anyway, so their FVs are still used Once
    
    -- Heap splitting
    -- ~~~~~~~~~~~~~~
    
    -- Assuming that we now have the correct and final entered information, we are in a position
    -- to decide how to split the heap. We are forced to output a residualisable heap binding if:
    --  1) EITHER it binds a variable free in the residual expression we have already committed to.
    --     Note that we do NOT have to residualise a binding if it binds something free only in
    --     the RHSs of some already-residual binding. Instead, we may want to float it in.
    --  2) OR it is a non-value with an overall demand of Many (taking into account demand from
    --     floats AND from already-residual bindings).
    --
    -- Anything else (a value or non-value with demand of Once) can be floated inwards into the
    -- Heaps of the appropriate float(s). We *may* still create a residual heap binding here if it
    -- turns out that the driven expressions still contained the binder as a free variable (as is
    -- typical with lazy supercompilation). This is handled by optimiseSplit.
    --
    -- Partition heap into values and non-values
    -- 1) Values *may* always be residualised or inlined
    -- 2) Non-values *must* be *either* inlined or residualised. You don't get a choice! They *may*
    --   be inlined only if:
    --    a) All things in h which refer to the non-value may also be inlined
    --    b) AND the non-value is used linearly, so sending down won't duplicate work
    --
    -- Of course, even if we *may* residualise/inline something, we should only *actually* do it if it is a free variable
    -- of the respective place.
    (h_value, h_nonvalue) = M.partition (taggedTermIsCheap . snd) h -- TODO: add cheapness analysis here instead, so we can deal with e.g. saturated datacon wrappers

    -- Split the non-value part of the heap into linear bindings it is safe to try to "send down", and non-linear ones we
    -- will have to residualise if they are ever actually referred to.
    (h_nonvalue_inlineable, h_nonvalue_noninlineable) = gather M.empty h_nonvalue
    gather h_inlineable h_undecided -- NB: these two heaps are disjoint
       -- Any non-value left undecided at this point must be unsafe to send down
      | M.null h_extra_inlineable = (h_inlineable, h_undecided)
       -- Send down any linear non-value we can ensure won't break the BV check
      | otherwise = gather (h_inlineable `M.union` h_extra_inlineable) h_undecided'
      where
        (h_extra_inlineable, h_undecided') = M.partitionWithKey (\x' _ -> doesnt_dup_work x') h_undecided
        doesnt_dup_work x' = maybe True isOnce (M.lookup x' entered')

    -- The h_nonvalue_noninlineable are the bindings which *ABSOLUTELY MUST* be residualised right now, because they are free
    -- in at least one place and furthermore are both expensive and may be used more than once. The free variables of those bindings
    -- are exactly what we need to feed to splitStack on the next iteration to ensure that things referred to by them
    -- but bound in the evaluation context are bound right here.
    --
    -- FIXME: must include the FVs of elements of h_inlineable that were not inlined into QA/Stack contexts due to generalisation.
    -- FIXME: surely should also contain FVs of h_value bindings reachable via h_nonvalue_noninlineable FVs?
    must_resid_k_xs' = S.unions $ map (inFreeVars taggedTermFreeVars) (M.elems h_nonvalue_noninlineable)

    -- Construct the final environment that is safe for inlining
    h_inlineable = h_value `M.union` h_nonvalue_inlineable


-- TODO: replace with a genuine evaluator. However, think VERY hard about the termination implications of this!
-- I think we can only do it when the splitter is being invoked by a non-whistling invocation of sc.
cheapifyHeap :: (Deeds, Heap) -> (Deeds, Heap)
cheapifyHeap (deeds, Heap h (splitIdSupply -> (ids, ids'))) = (deeds', Heap (M.fromList floats `M.union` h') ids')
  where
    ((deeds', _, floats), h') = M.mapAccum (\(deeds, ids, floats0) in_e -> case cheapify deeds ids in_e of (deeds, ids, floats1, in_e') -> ((deeds, ids, floats0 ++ floats1), in_e')) (deeds, ids, []) h
    
    -- TODO: make cheapification more powerful (i.e. deal with case bindings)
    cheapify :: Deeds -> IdSupply -> In TaggedTerm -> (Deeds, IdSupply, [(Out Var, In TaggedTerm)], In TaggedTerm)
    cheapify deeds0 ids0 (rn, Tagged tg (LetRec xes e)) = (deeds3, ids3, zip in_xs in_es' ++ floats0 ++ floats1, in_e')
      where deeds1 = releaseDeedDescend_ deeds0 tg
            (        ids1, rn', unzip -> (in_xs, in_es)) = renameBounds (\_ x' -> x') ids0 rn xes
            (deeds2, ids2, floats0, in_es') = cheapifyMany deeds1 ids1 in_es
            (deeds3, ids3, floats1, in_e')  = cheapify deeds2 ids2 (rn', e)
    cheapify deeds ids in_e = (deeds, ids, [], in_e)

    cheapifyMany :: Deeds -> IdSupply -> [In TaggedTerm] -> (Deeds, IdSupply, [(Out Var, In TaggedTerm)], [In TaggedTerm])
    cheapifyMany deeds ids = reassociate . mapAccumL ((associate .) . uncurry cheapify) (deeds, ids)
      where reassociate ((deeds, ids), unzip -> (floatss, in_es)) = (deeds, ids, concat floatss, in_es)
            associate (deeds, ids, floats, in_e) = ((deeds, ids), (floats, in_e))


splitStack :: Deeds
           -> IdSupply -> [Out Var]
           -> Stack
           -> (EnteredEnv, Bracketed State)
           -> (Deeds,
               M.Map (Out Var) (Bracketed State),
               (EnteredEnv, Bracketed State))
splitStack deeds _       _      []     (entered_hole, bracketed_hole) = (deeds, M.empty, (entered_hole, bracketed_hole)) -- \(rebuild, transfer, in_es) -> (rebuild, transfer, map (M.empty,[],) in_es)
splitStack deeds old_ids scruts (kf:k) (entered_hole, (Bracketed rebuild_hole extra_fvs_hole transfer_hole dstates_hole)) = case kf of
    Apply (Tagged _ x2') -> splitStack deeds old_ids [] k (entered_hole `plusEnteredEnv` mkEnteredEnv (Once Nothing) (S.singleton x2'), Bracketed (\es' -> rebuild_hole es' `app` x2') (S.insert x2' extra_fvs_hole) transfer_hole dstates_hole)
    -- NB: case scrutinisation is special! Instead of kontinuing directly with k, we are going to inline
    -- *as much of entire remaining evaluation context as we can* into each case branch. Scary, eh?
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    (if not (null k_not_inlined) then traceRender ("splitStack: generalise", k_not_inlined) else id) $
                                                    splitStack deeds' ids' [] (k_not_inlined ++ k_remaining) (entered_hole `plusEnteredEnv` mkEnteredEnv (Once (Just ctxt_id)) (S.unions $ zipWith (S.\\) alt_fvss alt_bvss), Bracketed (\(splitBy dstates_hole -> (es_hole', es_alt')) -> rebuild_alt (rebuild_hole es_hole') es_alt') extra_fvs_hole (\(splitBy dstates_hole -> (fvs_hole', fvs_alt')) -> transfer_alt (transfer_hole fvs_hole') fvs_alt') (dstates_hole ++ dstates_alts))
      where -- 0) Manufacture context identifier
            (ids', state_ids) = splitIdSupply old_ids
            ctxt_id = idFromSupply state_ids
        
            -- 1) Split the continuation eligible for inlining into two parts: that part which can be pushed into
            -- the case branch, and that part which could have been except that we need to refer to a variable it binds
            -- in the residualised part of the term we create
            (k_inlineable_candidates, k_remaining) = span (`does_not_bind_any_of` M.keysSet entered_hole) k
            does_not_bind_any_of (Update x') fvs = tagee x' `S.notMember` fvs
            does_not_bind_any_of _ _ = True
        
            -- 2) Construct the floats for each case alternative by pushing in that continuation
            (_alt_ids', alt_rns, alt_cons') = unzip3 $ map (renameAltCon ids' rn) alt_cons
            -- Bind something to the case scrutinee (if possible). This means that:
            --  let y = (\z -> case z of C -> ...) unk
            --  in y
            -- ===>
            --  case x of C -> let unk = C; z = C in ...
            alt_in_es = alt_rns `zip` alt_es
            alt_hs = zipWith3 (\alt_rn alt_con alt_tg -> M.fromList $ do { Just scrut_v <- [altConToValue alt_con]; scrut <- scruts; return (scrut, (alt_rn, Tagged alt_tg (Value scrut_v))) }) alt_rns alt_cons (map tag alt_es)
            (alt_bvss, alt_fvss) = unzip $ zipWith (\alt_con' (Heap alt_h _, alt_k, alt_in_e) -> altConOpenFreeVars alt_con' (pureHeapOpenFreeVars alt_h (stackFreeVars alt_k (inFreeVars taggedTermFreeVars alt_in_e)))) alt_cons' dstates_alts
            (deeds', k_not_inlined, dstates_alts) = go deeds k_inlineable_candidates (zipWith (\alt_h alt_in_e -> (Heap alt_h state_ids, [], alt_in_e)) alt_hs alt_in_es)
              where
                branch_factor = length alt_cons
                
                -- Inline parts of the evaluation context into each branch only if we can get that many deeds for duplication
                go deeds []     states = (deeds, [], states)
                go deeds (kf:k) states = case foldM (\deeds tag -> claimDeeds deeds tag (branch_factor - 1)) deeds (stackFrameTags kf) of -- NB: subtract one because one occurrence is already "paid for". It is OK if the result is negative (i.e. branch_factor 0)!
                    Nothing    -> traceRender ("splitStack: deed claim failure", length k) (deeds, kf:k, states)
                    Just deeds -> go deeds k (map (second3 (++ [kf])) states)
            
            -- 3) Define how to rebuild the case and transfer free variables out of it
            rebuild_alt e_hole' es_alt' = case_ e_hole' (zipWith (\alt_con' e_alt' -> (alt_con', e_alt')) alt_cons' es_alt')
            transfer_alt fvs_hole' fvss_alt' = fvs_hole' `S.union` S.unions (zipWith (\fvs_alt' alt_bvs -> fvs_alt' S.\\ alt_bvs) fvss_alt' alt_bvss)
    PrimApply pop in_vs in_es -> splitStack deeds ids' [] k (entered_hole `plusEnteredEnv` plusEnteredEnvs entered_vs `plusEnteredEnv` plusEnteredEnvs [mkEnteredEnv (Once $ Just ctxt_id) (inFreeVars taggedTermFreeVars in_e) | (ctxt_id, in_e) <- ctxt_ids `zip` in_es], Bracketed (\(splitBy dstates_hole -> (es_hole', es_args')) -> rebuild_pop (rebuild_hole es_hole') es_args') (extra_fvs_hole `S.union` S.unions (map extra_fvs bracketed_vss)) (\(splitBy dstates_hole -> (fvs_hole', fvss_args')) -> transfer_pop (transfer_hole fvs_hole') fvss_args') (dstates_hole ++ dstates_vs ++ dstates_es))
      where -- 0) Manufacture context identifier
            (ids', state_idss) = accumL splitIdSupply old_ids (length in_es)
            ctxt_ids = map idFromSupply state_idss
            
            -- 1) Split every value remaining apart
            (entered_vs, bracketed_vss {- unzip4 -> (rebuilds_vs, extra_fvss_vs, transfers_vs, dstatess_vs) -}) = unzip $ map (splitValue ids' . tagee) in_vs
            
            -- 2) Define how to rebuild the primitive application
            dstates_vss = map fillers bracketed_vss
            dstates_vs = concat dstates_vss
            dstates_es = [(Heap M.empty state_ids, [], in_e) | (state_ids, in_e) <- state_idss `zip` in_es]
            rebuild_pop e_hole' (splitBy dstates_vs -> (splitManyBy dstates_vss -> es_vs', es_es')) = primOp pop (zipWith ($) (map rebuild bracketed_vss) es_vs' ++ [e_hole'] ++ es_es')
            transfer_pop fvs_hole' (splitBy dstates_vs -> (fvss_vs', fvs_es')) = fvs_hole' `S.union` S.unions (zipWith ($) (map transfer bracketed_vss) $ splitManyBy dstates_vss fvss_vs') `S.union` S.unions fvs_es'
    Update (Tagged _ x') -> second3 (M.insert x' (Bracketed rebuild_hole extra_fvs_hole transfer_hole dstates_hole)) $ splitStack deeds old_ids (x' : scruts) k (entered_hole `M.union` mkEnteredEnv (Once Nothing) (S.singleton x'), Bracketed (\[] -> var x') (S.singleton x') (\[] -> S.empty) [])
  where
    altConToValue :: AltCon -> Maybe (ValueF ann)
    altConToValue (DataAlt dc xs) = Just $ Data dc xs
    altConToValue (LiteralAlt l)  = Just $ Literal l
    altConToValue (DefaultAlt _)  = Nothing

splitValue :: IdSupply -> In TaggedValue -> (EnteredEnv, Bracketed State)
splitValue ids in_v@(rn, Lambda x e) = (mkEnteredEnv (Many False) (inFreeVars taggedValueFreeVars in_v), Bracketed (\[h] -> lambda x' h) S.empty (\[fvs] -> S.delete x' fvs) [(Heap M.empty state_ids', [], (rn', e))])
  where (state_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v                  = (mkEnteredEnv (Once Nothing) fvs', Bracketed (\[] -> value v') fvs' (\[] -> S.empty) [])
  where v' = detagValue $ renameIn renameTaggedValue ids in_v
        fvs' = valueFreeVars v'

splitQA :: IdSupply -> Tagged QA -> (EnteredEnv, Bracketed State)
splitQA _   (Tagged _ (Question x')) = (mkEnteredEnv (Once Nothing) (S.singleton x'), Bracketed (\[] -> var x') (S.singleton x') (\[] -> S.empty) [])
splitQA ids (Tagged _ (Answer in_v)) = splitValue ids in_v
