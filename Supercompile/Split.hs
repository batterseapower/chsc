{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Split (split) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate (step)
import Evaluator.FreeVars
import Evaluator.Syntax

import Name
import Renaming
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


--
-- == Gathering entry information for the splitter ==
--

data Entered = Once (Maybe Id) -- ^ The Id is a context identifier: if a binding is Entered twice from the same context it's really a single Entrance. Nothing signifies the residual context (i.e. there is no associated float)
             | Many
             deriving (Eq, Show)

instance Pretty Entered where
    pPrint = text . show

isOnce :: Entered -> Bool
isOnce (Once _) = True
isOnce _ = False

plusEntered :: Entered -> Entered -> Entered
plusEntered (Once mb_id1) (Once mb_id2)
  | mb_id1 == mb_id2 = Once mb_id1
  | otherwise        = {- traceRender ("Once promotion", mb_id1, mb_id2) -} Many
plusEntered _ _ = Many

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


split :: Monad m
      => (State -> m (FreeVars, Out Term))
      -> State
      -> m (FreeVars, Out Term)
split opt (simplify -> (Heap h ids, k, qa)) = uncurry3 optimiseSplit (split' opt (Heap h ids) k (splitQA ids qa))

-- Non-expansive simplification that we can safely do just before splitting to make the splitter a bit simpler
data QA = Question (Out Var)
        | Answer   (In TaggedValue)

simplify :: State -> (Heap, Stack, Tagged QA)
simplify s = expectHead "simplify" [res | s <- s : unfoldr (\s -> fmap (\x -> (x, x)) (step s)) s, Just res <- [stop s]]
  where
    stop (h, k, (rn, TaggedTerm (Tagged tg (Var x))))   = Just (h, k, Tagged tg (Question (rename rn x)))
    stop (h, k, (rn, TaggedTerm (Tagged tg (Value v)))) = Just (h, k, Tagged tg (Answer (rn, v)))
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
    fillers :: [a]                      -- Hole-fillers themselves. Can be In TaggedTerm, State or DrivePureState
  }

instance Functor Bracketed where
    fmap f b = b { fillers = map f (fillers b) }

optimiseBracketed :: Monad m
                  => (State -> m (FreeVars, Out Term))
                  -> Bracketed State
                  -> m (FreeVars, Out Term)
optimiseBracketed opt b = do
    (fvs', es') <- liftM unzip $ mapM opt (fillers b)
    return (extra_fvs b `S.union` transfer b fvs', rebuild b es')

-- We are going to use this helper function to inline any eligible inlinings to produce the expressions for driving
transitiveInline :: PureHeap -> PureHeap -> FreeVars -> PureHeap
transitiveInline h_inlineable h_output fvs
    = if M.null h_inline then h_output else transitiveInline h_inlineable' (h_inline `M.union` h_output) fvs'
  where (h_inline, h_inlineable') = M.partitionWithKey (\x' _ -> x' `S.member` fvs) h_inlineable
        fvs' = M.fold (\in_e fvs -> fvs `S.union` inFreeVars taggedTermFreeVars in_e) S.empty h_inline

transitiveInline' :: PureHeap -> State -> State
transitiveInline' h_inlineable state@(Heap h ids, k, in_e) = (Heap (transitiveInline (h_inlineable `M.union` h) M.empty (stateFreeVars state)) ids, k, in_e)

optimiseSplit :: Monad m
              => (Bracketed PureState -> m (FreeVars, Out Term))
              -> M.Map (Out Var) (Bracketed PureState)
              -> Bracketed PureState
              -> m (FreeVars, Out Term)
optimiseSplit optimise_bracketed floats_h floats_compulsory = do
    -- 1) Recursively drive the compulsory floats
    (fvs_compulsory', e_compulsory') <- optimise_bracketed floats_compulsory
    
    -- 2) We now need to think about how we are going to residualise the letrec. We only want to drive (and residualise) as
    --    much as we actually refer to. This loop does this: it starts by residualising the free variables of the compulsory
    --    residualisation, and then transitively inlines any bindings whose corresponding binders become free.
    let residualise xes_resid resid_bvs resid_fvs
          | M.null h_resid = -- traceRenderM ("residualise", resid_fvs, resid_bvs, (M.map (residualiseBracketed (residualiseState . first3 (flip Heap prettyIdSupply))) floats_h)) $
                             return (resid_fvs S.\\ resid_bvs, xes_resid)
          | otherwise = {- traceRender ("optimiseSplit", xs_resid') $ -} do
            -- Recursively drive the new residuals arising from the need to bind the resid_fvs
            (S.unions -> extra_resid_fvs', es_resid') <- liftM unzip $ mapM optimise_bracketed bracks_resid
            -- Recurse, because we might now need to residualise and drive even more stuff (as we have added some more FVs and BVs)
            residualise (xes_resid ++ zip xs_resid' es_resid')
                        (resid_bvs `S.union` M.keysSet h_resid)
                        (resid_fvs `S.union` extra_resid_fvs')
          where
            -- When assembling the final list of things to drive, ensure that we exclude already-driven things
            h_resid = M.filterWithKey (\x _br -> x `S.member` resid_fvs) (floats_h `exclude` resid_bvs)
            (xs_resid', bracks_resid) = unzip $ M.toList h_resid

    (fvs', xes') <- residualise [] S.empty fvs_compulsory'
    return (fvs', letRec xes' e_compulsory')

-- Whether the given variable was entered many times, with no context identifier information required
-- I'm using this abstraction to make explicit the fact that we don't pass context identifiers between
-- iterations of the splitter "go" loop. This is important because they are potentially unstable!
type EnteredManyEnv = M.Map (Out Var) Bool

toEnteredManyEnv :: EnteredEnv -> EnteredManyEnv
toEnteredManyEnv = M.map (not . isOnce)

split'
  :: Monad m
  => (State -> m (FreeVars, Out Term))
  -> Heap
  -> Stack
  -> (EnteredEnv, Bracketed PureState)
  -> (Bracketed PureState -> m (FreeVars, Out Term),
      M.Map (Out Var) (Bracketed PureState),
      Bracketed PureState)
split' opt (cheapifyHeap -> Heap h (splitIdSupply -> (ids1, ids2))) k (entered_hole, bracketed_hole)
  = go S.empty (toEnteredManyEnv entered_hole)
  where
    go must_resid_k_xs entered_many
      -- | traceRender ("split.go", entered, entered_k, xs_nonvalue_inlinings) False = undefined
      | entered_many == entered_many'
      , must_resid_k_xs == must_resid_k_xs'
      = -- (\res -> traceRender ("split'", entered_hole, "==>", entered_k, "==>", entered', must_resid_k_xs, [x' | Tagged _ (Update x') <- k], M.keysSet floats_k_bound) res) $
        (\brack -> do
          (fvs', e') <- optimiseBracketed opt (fmap (\(h, k, in_e) -> transitiveInline' h_inlineable (Heap h ids2, k, in_e)) brack)
          let _xs_upd_frames_pushed_down = S.fromList [x' | Tagged _ (Update x') <- k] S.\\ M.keysSet floats_k_bound
          assertRender ("optimiseBracketed", fvs' `S.intersection` _xs_upd_frames_pushed_down) (S.null (fvs' `S.intersection` _xs_upd_frames_pushed_down)) $ return ()
          return (fvs', e'),
         M.map promoteToBracket (h `exclude` xs_nonvalue_inlinings) `M.union` floats_k_bound,
         bracket_k)
      | otherwise = go must_resid_k_xs' entered_many'
      where
        -- Evaluation context splitting
        -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        
        -- Guess how to split up the evaluation context, based on residualising those update frames
        -- that bound any variables free the last time around the loop.
        -- NB: we add the FVs of the part of the heap that we *have* to residualise to the entered_hole
        -- information. This ensures that splitStack residualises the update frames for any of
        -- those FVs that it happens to bind, which is essential for correctness.
        (floats_k_bound, (entered_k, bracket_k)) = splitStack ids1 Nothing k (entered_hole `plusEnteredEnv` mkEnteredEnv (Once Nothing) must_resid_k_xs, bracketed_hole)
        
        -- Heap splitting
        -- ~~~~~~~~~~~~~~
        
        -- Guess which parts of the heap are safe for inlining based on the current Entered information
        (h_inlineable, entered', must_resid_k_xs') = splitPureHeap h entered_many entered_k
        
        -- NB: We must NOT take non-values that we have decided to inline and then bind them in the residual term. This does not
        -- usually happen because such things won't be free variables of the immediate output term, but with strict bindings the
        -- optimiser will be forced to residualise such bindings anyway. Explicitly filter them out to be sure we don't spuriously
        -- recompute such bindings, BUT make sure to retain non-value bindings that are used Once by the *residual itself*:
        xs_nonvalue_inlinings = M.keysSet $ M.filterWithKey (\x (_, e) -> maybe False (/= Once Nothing) (M.lookup x entered') && not (taggedTermIsCheap e)) h_inlineable
        
        entered_many' = toEnteredManyEnv entered'

    promoteToPureState :: In TaggedTerm -> PureState
    promoteToPureState in_e = (M.empty, [], in_e)

    promoteToBracket :: In TaggedTerm -> Bracketed PureState
    promoteToBracket in_e = Bracketed (\[e'] -> e') S.empty (\[fvs'] -> fvs') [promoteToPureState in_e]

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
                                         mkEnteredEnv (if taggedTermIsCheap (snd in_e) && was_many then Many else Once (Just i)) (inFreeVars taggedTermFreeVars in_e)
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
    must_resid_k_xs' = S.unions $ map (inFreeVars taggedTermFreeVars) (M.elems h_nonvalue_noninlineable)

    -- Construct the final environment that is safe for inlining
    h_inlineable = h_value `M.union` h_nonvalue_inlineable


-- TODO: replace with a genuine evaluator
cheapifyHeap :: Heap -> Heap
cheapifyHeap (Heap h (splitIdSupply -> (ids, ids'))) = Heap (M.fromList floats `M.union` h') ids'
  where
    ((_, floats), h') = M.mapAccum (\(ids, floats0) (r, in_e) -> case cheapify ids (r, in_e) of (ids, floats1, (r', in_e')) -> ((ids, floats0 ++ floats1), (r', in_e'))) (ids, []) h
    
    -- TODO: make cheapification more powerful (i.e. deal with case bindings)
    cheapify :: IdSupply -> (In TaggedTerm) -> (IdSupply, [(Out Var, In TaggedTerm)], In TaggedTerm)
    cheapify ids0 (rn, TaggedTerm (Tagged _ (LetRec xes e))) = (ids3, zip in_xs in_es' ++ floats0 ++ floats1, in_e')
      where (ids1, rn', unzip -> (in_xs, in_es)) = renameBounds (\_ x' -> x') ids0 rn xes
            (ids2, floats0, in_es') = cheapifyMany ids1 in_es
            (ids3, floats1, in_e') = cheapify ids2 (rn', e)
    cheapify ids in_e = (ids, [], in_e)

    cheapifyMany :: IdSupply -> [In TaggedTerm] -> (IdSupply, [(Out Var, In TaggedTerm)], [In TaggedTerm])
    cheapifyMany ids = reassociate . mapAccumL ((associate .) . cheapify) ids
      where reassociate (ids, unzip -> (floatss, in_es)) = (ids, concat floatss, in_es)
            associate (ids, floats, in_e) = (ids, (floats, in_e))


splitStack :: IdSupply -> Maybe (Out Var)
           -> Stack
           -> (EnteredEnv, Bracketed PureState)
           -> (M.Map (Out Var) (Bracketed PureState),
               (EnteredEnv, Bracketed PureState))
splitStack _       _           []               (entered_hole, bracketed_hole) = (M.empty, (entered_hole, bracketed_hole)) -- \(rebuild, transfer, in_es) -> (rebuild, transfer, map (M.empty,[],) in_es)
splitStack old_ids mb_in_scrut (Tagged tg kf:k) (entered_hole, (Bracketed rebuild_hole extra_fvs_hole transfer_hole dstates_hole)) = case kf of
    Apply x2' -> splitStack old_ids Nothing k (entered_hole `plusEnteredEnv` mkEnteredEnv (Once Nothing) (S.singleton x2'), Bracketed (\es' -> rebuild_hole es' `app` x2') (S.insert x2' extra_fvs_hole) transfer_hole dstates_hole)
    -- NB: case scrutinisation is special! Instead of kontinuing directly with k, we are going to inline
    -- *as much of entire remaining evaluation context as we can* into each case branch. Scary, eh?
    Scrutinise (rn, unzip -> (alt_cons, alt_es)) -> -- (if null k_remaining then id else traceRender ("splitStack: FORCED SPLIT", M.keysSet entered_hole, [x' | Tagged _ (Update x') <- k_remaining])) $
                                                    splitStack ids' Nothing k_remaining (entered_hole `plusEnteredEnv` mkEnteredEnv (Once (Just ctxt_id)) (S.unions $ zipWith (S.\\) alt_fvss alt_bvss), Bracketed (\(splitBy dstates_hole -> (es_hole', es_alt')) -> rebuild_alt (rebuild_hole es_hole') es_alt') extra_fvs_hole (\(splitBy dstates_hole -> (fvs_hole', fvs_alt')) -> transfer_alt (transfer_hole fvs_hole') fvs_alt') (dstates_hole ++ dstates_alts))
      where -- 0) Manufacture context identifier
            (ids', ctxt_id) = stepIdSupply old_ids
        
            -- 1) Split the continuation eligible for inlining into two parts: that part which can be pushed into
            -- the case branch, and that part which could have been except that we need to refer to a variable it binds
            -- in the residualised part of the term we create
            (k_inlineable, k_remaining) = span (`does_not_bind_any_of` M.keysSet entered_hole) k
            does_not_bind_any_of (Tagged _ (Update x')) fvs = x' `S.notMember` fvs
            does_not_bind_any_of _ _ = True
        
            -- 2) Construct the floats for each case alternative by pushing in that continuation
            (_alt_ids', alt_rns, alt_cons') = unzip3 $ map (renameAltCon ids' rn) alt_cons
            -- Bind something to the case scrutinee (if possible). This means that:
            --  let y = (\z -> case z of C -> ...) unk
            --  in y
            -- ===>
            --  case x of C -> let unk = C; z = C in ...
            alt_in_es = alt_rns `zip` alt_es
            alt_hs = zipWith (\alt_rn alt_con -> M.empty `fromMaybe` do { in_scrut <- mb_in_scrut; scrut_v <- altConToValue alt_con; return (M.singleton in_scrut (alt_rn, TaggedTerm $ Tagged tg $ Value $ scrut_v)) }) alt_rns alt_cons
            (alt_bvss, alt_fvss) = unzip $ zipWith3 (\alt_con' alt_h alt_in_e -> altConOpenFreeVars alt_con' (pureHeapOpenFreeVars alt_h (stackFreeVars k_inlineable (inFreeVars taggedTermFreeVars alt_in_e)))) alt_cons' alt_hs alt_in_es
            dstates_alts = zip3 alt_hs (repeat k_inlineable) alt_in_es
            
            -- 3) Define how to rebuild the case and transfer free variables out of it
            rebuild_alt e_hole' es_alt' = case_ e_hole' (zipWith (\alt_con' e_alt' -> (alt_con', e_alt')) alt_cons' es_alt')
            transfer_alt fvs_hole' fvss_alt' = fvs_hole' `S.union` S.unions (zipWith (\fvs_alt' alt_bvs -> fvs_alt' S.\\ alt_bvs) fvss_alt' alt_bvss)
    PrimApply pop in_vs in_es -> splitStack ids' Nothing k (entered_hole `plusEnteredEnv` plusEnteredEnvs entered_vs `plusEnteredEnv` plusEnteredEnvs [mkEnteredEnv (Once $ Just ctxt_id) (inFreeVars taggedTermFreeVars in_e) | (ctxt_id, in_e) <- ctxt_ids `zip` in_es], Bracketed (\(splitBy dstates_hole -> (es_hole', es_args')) -> rebuild_pop (rebuild_hole es_hole') es_args') (extra_fvs_hole `S.union` S.unions (map extra_fvs bracketed_vss)) (\(splitBy dstates_hole -> (fvs_hole', fvss_args')) -> transfer_pop (transfer_hole fvs_hole') fvss_args') (dstates_hole ++ dstates_vs ++ dstates_es))
      where -- 0) Manufacture context identifier
            (ids', ctxt_ids) = accumL stepIdSupply old_ids (length in_es)
            
            -- 1) Split every value remaining apart
            (entered_vs, bracketed_vss {- unzip4 -> (rebuilds_vs, extra_fvss_vs, transfers_vs, dstatess_vs) -}) = unzip $ map (splitValue ids') in_vs
            
            -- 2) Define how to rebuild the primitive application
            dstates_vss = map fillers bracketed_vss
            dstates_vs = concat dstates_vss
            dstates_es = [(M.empty, [], in_e) | in_e <- in_es]
            rebuild_pop e_hole' (splitBy dstates_vs -> (splitManyBy dstates_vss -> es_vs', es_es')) = primOp pop (zipWith ($) (map rebuild bracketed_vss) es_vs' ++ [e_hole'] ++ es_es')
            transfer_pop fvs_hole' (splitBy dstates_vs -> (fvss_vs', fvs_es')) = fvs_hole' `S.union` S.unions (zipWith ($) (map transfer bracketed_vss) $ splitManyBy dstates_vss fvss_vs') `S.union` S.unions fvs_es'
    Update x' -> first (M.insert x' (Bracketed rebuild_hole extra_fvs_hole transfer_hole dstates_hole)) $ splitStack old_ids (Just x') k (entered_hole `M.union` mkEnteredEnv (Once Nothing) (S.singleton x'), Bracketed (\[] -> var x') (S.singleton x') (\[] -> S.empty) [])
  where
    altConToValue :: AltCon -> Maybe (ValueF term)
    altConToValue (DataAlt dc xs) = Just $ Data dc xs
    altConToValue (LiteralAlt l)  = Just $ Literal l
    altConToValue (DefaultAlt _)  = Nothing

splitValue :: IdSupply -> In TaggedValue -> (EnteredEnv, Bracketed PureState)
splitValue ids in_v@(rn, Lambda x e) = (mkEnteredEnv Many (inFreeVars taggedValueFreeVars in_v), Bracketed (\[h] -> lambda x' h) S.empty (\[fvs] -> S.delete x' fvs) [(M.empty, [], (rn', e))])
  where (_ids', rn', x') = renameBinder ids rn x
splitValue ids in_v                  = (mkEnteredEnv (Once Nothing) fvs', Bracketed (\[] -> value v') fvs' (\[] -> S.empty) [])
  where v' = detagValue $ renameIn renameTaggedValue ids in_v
        fvs' = valueFreeVars v'

splitQA :: IdSupply -> Tagged QA -> (EnteredEnv, Bracketed PureState)
splitQA _   (Tagged _ (Question x')) = (mkEnteredEnv (Once Nothing) (S.singleton x'), Bracketed (\[] -> var x') (S.singleton x') (\[] -> S.empty) [])
splitQA ids (Tagged _ (Answer in_v)) = splitValue ids in_v
