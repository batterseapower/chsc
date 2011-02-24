{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards, BangPatterns, RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Drive (SCStats(..), supercompile) where

import Supercompile.Match
import Supercompile.Split

import Core.FreeVars
import Core.Prettify
import Core.Renaming
import Core.Syntax
import Core.Tag

import Evaluator.Deeds
import Evaluator.Evaluate
import Evaluator.FreeVars
import Evaluator.Residualise
import Evaluator.Syntax

import Termination.TagBag
import Termination.TagGraph
import Termination.TagSet
import Termination.Terminate
import Termination.Generaliser

import Name
import Renaming
import StaticFlags
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Map as M
import Data.Monoid
import Data.Ord
import qualified Data.Set as S
import qualified Data.IntSet as IS


-- The termination argument is a but subtler due to HowBounds but I think it still basically works.
-- Key to the modified argument is that tieback cannot be prevented by any HeapBinding with HowBound /= LambdaBound:
-- so we have to be careful to record tags on those guys.
wQO :: WQO State Generaliser
wQO | not tERMINATION_CHECK                        = postcomp (const generaliseNothing) unsafeNever
    | otherwise = case tAG_COLLECTION of TagBag       -> embedWithTagBags
                                         TagBagStrong -> embedWithTagBagsStrong
                                         TagGraph     -> embedWithTagGraphs
                                         TagSet       -> embedWithTagSets


data SCStats = SCStats {
    stat_reduce_stops :: Int,
    stat_sc_stops :: Int
  }

instance Monoid SCStats where
    mempty = SCStats {
        stat_reduce_stops = 0,
        stat_sc_stops = 0
      }
    stats1 `mappend` stats2 = SCStats {
        stat_reduce_stops = stat_reduce_stops stats1 + stat_reduce_stops stats2,
        stat_sc_stops = stat_sc_stops stats1 + stat_sc_stops stats2
      }


supercompile :: Term -> (SCStats, Term)
supercompile e = traceRender ("all input FVs", input_fvs) $ second (fVedTermToTerm . if pRETTIFY then prettify else id) $ runScpM $ liftM snd $ sc (mkHistory (extra wQO)) state
  where input_fvs = annedTermFreeVars anned_e
        state = normalise ((bLOAT_FACTOR - 1) * annedSize anned_e, Heap (setToMap environmentallyBound input_fvs) reduceIdSupply, [], (mkIdentityRenaming $ S.toList input_fvs, anned_e))
        anned_e = toAnnedTerm e

--
-- == Bounded multi-step reduction ==
--

-- We used to garbage-collect in the evaluator, when we executed the rule for update frames. This had two benefits:
--  1) We don't have to actually update the heap or even claim a new deed
--  2) We make the supercompiler less likely to terminate, because GCing so tends to reduce TagBag sizes
--
-- However, this caused problems with speculation: to prevent incorrectly garbage collecting bindings from the invisible "enclosing"
-- heap when we speculated one of the bindings from the heap, we had to pass around an extra "live set" of parts of the heap that might
-- be referred to later on. Furthermore:
--  * Finding FVs when executing every update step was a bit expensive (though they were memoized on each of the State components)
--  * This didn't GC cycles (i.e. don't consider stuff from the Heap that was only referred to by the thing being removed as "GC roots")
--  * It didn't seem to make any difference to the benchmark numbers anyway
--
-- You might think a good alternative approach is to:
-- 1. Drop dead update frames in transitiveInline (which is anyway responsible for ensuring there is no dead stuff in the stack)
-- 2. "Squeeze" just before the matcher: this shorts out indirections-to-indirections and does update-frame stack squeezing.
--    You might also think that it would be cool to just do this in normalisation, but then when normalising during specualation the enclosing
--    context wouldn't get final_rned :-(
--
-- HOWEVER. That doesn't work properly because normalisation itself can introduce dead bindings - i.e. in order to be guaranteed to
-- catch all the junk we have to GC normalised bindings, not the pre-normalised ones that transitiveInline sees. So the new plan is to do
-- both points 1 and 2 right just before we go to the matcher.
--
-- TODO: have the garbage collector collapse (let x = True in x) to (True) -- but note that this requires onceness analysis
gc :: State -> State
gc _state@(deeds0, Heap h ids, k, in_e) = assertRender ("gc: free vars", stateFreeVars _state S.\\ stateFreeVars state') (stateFreeVars _state `S.isSubsetOf` stateFreeVars state')
                                          assertRender ("gc: uncovered vars", final_rn, stateUncoveredVars state', pPrintFullState _state, pPrintFullState state') (S.null (stateUncoveredVars state'))
                                          state'
  where
    state' = (deeds2, Heap h' ids, k', renameInRenaming final_rn in_e)
    
    rn0 = emptyRenaming
    -- We need to filter out update frames here or the lives won't include those things bound by k. This would mean that stack frames
    -- binding stuff only used by in_e would look dead to us... (this bit me in Generalisation.core, among others)
    live0 = stateFreeVars (deeds0, Heap M.empty ids, [kf | kf <- k, case tagee kf of Update _ -> False; _ -> True], in_e)
    (rn1, deeds1, h', live1) = inlineLiveHeap rn0 deeds0 h live0
    -- Collecting dead update frames doesn't make any new heap bindings dead since they don't refer to anything
    (final_rn {- NB: loop through this variable -}, deeds2, k') = pruneLiveStack rn1 deeds1 k live1
    
    -- The threaded renamings map ORIGINAL variables to INTERMEDIATE ones. You shouldn't look at those!
    -- The final renaming maps ORIGINAL variables to FINALISED ones
    -- The live set tests on ORIGINAL variables only
    
    inlineLiveHeap :: Renaming -> Deeds -> PureHeap -> FreeVars -> (Renaming, Deeds, PureHeap, FreeVars)
    inlineLiveHeap rn deeds h live = -- traceRender ("inlineLiveHeap", h, live, M.keysSet h_live, live')
                                     (rn', deeds `releasePureHeapDeeds` h_dead, h_live, live')
      where
        (rn', h_dead, h_live, live') = heap_worker rn h M.empty live
        
        -- This is just like Split.transitiveInline, but simpler since it never has to worry about running out of deeds:
        heap_worker :: Renaming -> PureHeap -> PureHeap -> FreeVars -> (Renaming, PureHeap, PureHeap, FreeVars)
        heap_worker rn h_pending h_output live
          = if live == live'
            then (rn', h_pending', h_output', live')
            else heap_worker rn' h_pending' h_output' live'
          where 
            (rn', h_pending_kvs', h_output', live') = M.foldrWithKey consider_inlining (rn, [], h_output, live) h_pending
            h_pending' = M.fromDistinctAscList h_pending_kvs'
        
            consider_inlining x' hb (rn, h_pending_kvs, h_output, live)
              | x' `S.member` live
              , Nothing <- rename_maybe rn x' -- Ensure that we don't try to short out indirections twice
              = case heapBindingTerm hb of
                  Just (e_rn, e) | Just y <- termToVar e
                                 , let final_y' = rename (final_rn `renameRenaming` e_rn) y
                                       y'       = rename e_rn                             y
                                 -- , traceRender ("gc: variable in heap", x', y') True
                                 -> (insertRenaming x' final_y' rn, (x', hb) : h_pending_kvs,                                             h_output, S.insert y' live)
                  _              -> (rn,                                       h_pending_kvs, M.insert x' (renameHeapBinding final_rn hb) h_output, live `S.union` heapBindingFreeVars hb)
              | otherwise = (rn, (x', hb) : h_pending_kvs, h_output, live)
    
    pruneLiveStack :: Renaming ->  Deeds -> Stack -> FreeVars -> (Renaming, Deeds, Stack)
    pruneLiveStack rn deeds k live = (rn', deeds `releaseStackDeeds` k_dead, k_live)
      where
        (rn', k_dead, k_live) = stack_worker rn k
        
        stack_worker rn [] = (rn, [], [])
        stack_worker rn (kf:k)
           -- Eliminate dead stack frames
          | Update x' <- tagee kf
          , x' `S.notMember` live
          = second3 (kf:) $ stack_worker rn k
           -- Collapse nested stack frames (GHC calls this "stack squeezing")
          | Update x' <- tagee kf
          , (kf':k') <- k
          , Update y' <- tagee kf'
          -- , traceRender ("gc: update frame squeezing", x', y') True
          -- NB: by recursing with kf at the front, we avoid a bugs that might happen if kf' was not live but
          -- kf was, where kf would be dropped as dead (bit me in SpeculationWorstCase)
          = second3 (kf':) $ stack_worker (insertRenaming y' (renameIfPresent final_rn x') rn) (kf:k')
           -- Keep any other stack frames
          | otherwise
          = third3 (fmap (renameStackFrame final_rn) kf:) $ stack_worker rn k

type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


speculate :: (State -> (SCStats, State))
          -> State -> (SCStats, State)
speculate reduce = snd . go (0 :: Int) (mkHistory wQO) (emptyLosers, S.empty)
  where
    go depth hist (losers, speculated) state = case terminate hist state of
        Continue hist' -> continue depth hist' (losers, speculated) state
        _              -> ((hist, losers, speculated), (mempty, state)) -- We MUST NOT EVER reduce in this branch or speculation will loop on e.g. infinite map
    
    continue depth hist (losers, speculated) state = -- traceRender ("speculate:continue", pPrintFullState state, pPrintFullState _state')
                                                     assertRender (hang (text "speculate: deeds lost or gained:") 2 (pPrint state $$ pPrint state''))
                                                                  (noChange (releaseStateDeed state) (releaseStateDeed state'')) $
                                                     ((threaded_hist', losers', speculated'), (stats', state''))
      where
        (stats, _state'@(deeds', Heap h' ids', k, in_e)) = reduce state
        state'' = (deeds'', Heap (h'_winners' `M.union` h'_losers) ids'', k, in_e)
        
        -- Note [Controlling speculation]
        -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        --
        -- Speculation gets out of hand easily. A motivating example is DigitsOfE2: without some way to control
        -- speculation, it blows up, and I have not observed it to terminate.
        --
        -- One approach is using "losers". In this approach, we prevent speculation from forcing heap-carried things
        -- that have proved to be losers in the past, as indicated by their tags being part of an accumulated losers set.
        -- The losers set was threaded through "go", and hence generated anew for each call to "speculate".
        --
        -- An attractive approach (inspired by Simon, as usual!) is to just thread the *history* through go. This should have a
        -- similiar effect, but prevents multiplication of mechanisms.
        --
        -- In my tests, the losers set approach ensured that DigitsOfE2 terminated after ~13s. Changing to the threaded
        -- history approach, I did not observe termination :-(
        (h'_losers, h'_winners) | sPECULATE_ON_LOSERS = (M.empty, h')
                                | otherwise           = M.partition (\hb -> maybe False (`IS.member` losers) (heapBindingTag hb)) h'
        
        -- Note [Order of speculation]
        -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~
        --
        -- It is quite important that are insensitive to dependency order. For example:
        --
        --  let id x = x
        --      idish = id id
        --  in e
        --
        -- If we speculated idish first without any information about what id is, it will be irreducible. If we do it the other way
        -- around (or include some information about id) then we will get a nice lambda. This is why we speculate each binding with
        -- *the entire rest of the heap* also present.
        
        -- TODO: I suspect we should accumulate Losers across the boundary of speculate as well
        -- TODO: there is a difference between losers due to termination-halting and losers because we didn't have enough
        -- information available to complete evaluation
        -- TODO: speculation could be more efficient if I could see the bindings that I speculated on the last invocation of the speculate function
        (stats', deeds'', Heap h'_winners' ids'', threaded_hist', losers', speculated') = M.foldrWithKey speculate_one (stats, deeds', Heap h'_winners ids', hist, losers, speculated) h'_winners
        speculate_one x' hb (stats, deeds, Heap h'_winners ids, threaded_hist, losers, speculated)
          -- | not (isValue (annee (snd in_e))), traceRender ("speculate", x', depth, pPrintFullUnnormalisedState (Heap (h {- `exclude` M.keysSet base_h -}) ids, k, in_e)) False = undefined
          | InternallyBound <- howBound hb
          , Just (_, annedTag -> tg) <- heapBindingTerm hb
          , x' `S.notMember` speculated
          , let e_x' = annedTerm tg (Var x')
          , Just deeds <- claimDeeds deeds (annedSize e_x') -- We have to pay for the syntax we use to start the speculation!! Small but subtle point that makes a big difference.
          , let -- We're going to be a bit clever here: to speculate a heap binding, just put that variable into the focus and reduce the resulting term.
                -- The only complication occurs when comes back with a non-empty stack, in which case we need to deal with any unreduced update frames.
                ((threaded_hist', losers', speculated'), (stats', state'@(_, _, k, _))) = go (depth + 1) (if tHREAD_SPECULATOR_HISTORY then threaded_hist else hist) (losers, S.insert x' speculated) (normalise (deeds, Heap h'_winners ids, [], (mkIdentityRenaming [x'], e_x')))
                -- Update frames present in the output indicate a failed speculation attempt. (Though if a var is the focus without an update frame yet that is also failure of a sort...)
                --
                -- Old Plan
                -- ~~~~~~~~
                -- I used to restore the original input bindings for variables bound by remaining update frames. We also added them to the speculated set so we don't bother looking again. Note that this might make
                -- some heap bindings dead (because they are referred to by the overwritten terms), but we'll just live with that and have the GC clean it up later (pessimising deeds a bit, but never mind).
                --
                -- More seriously, one of the update frames could be for a heap binding not present in the h'_winners. If anything in the new heap h' might refer to that, we have to be careful.
                -- One case is that that heap binding is referred to only by bindings that are made dead by the restoration - consider:
                --
                --  x |-> let y = ... z ...; z = unk in case z of ...
                --
                -- Speculating x will fail (blocked on unk) with update frames for x and z on the stack. We can't restore the z binding here, because it wasn't in the input heap, but the output
                -- heap will contain a y binding that refers to z. This is (just barely) OK because those new unbound FVs wont ACTUALLY be reachable. When we roll back to the original x RHS the
                -- y binding will just become dead.
                --
                -- However, this isn't OK:
                --
                --  xs |-> let ys = e in 1 : ys
                --  foo |-> last xs
                --
                -- Let's speculate foo:
                --
                --  xs |-> 1 : ys
                --  ys |-> e
                --  foo |-> last ys
                --
                -- Let's say we stop before evalutating e further, with update frames for foo and ys present. We can restore the original foo binding, but that will leave xs with a dangling
                -- reference to the ys binding that we couldn't restore. Argh!
                --
                -- What I did in this situation is to "agressively" roll back, discarding work done by the nested reduce and any things it added to the speculated set.
                -- I hoped this case didn't hit too often so it won't slow speculation down. Unfortunately after some changes to the normaliser it hit *all* *the* *time* in e.g. SpeculationWorstCase
                -- and made the supercompiler non-terminate.
                --
                -- New Plan
                -- ~~~~~~~~
                -- The new plan is to give up on this nonsense and just reconstruct a new heap from the output of recursive speculation. The disadvantages of this approach are:
                --  * We might bloat output terms a bit because versions of terms that failed speculation will stick around
                --  * We might end up spuriously reducing the same binding every time we recurse in sc because we get a chance to speculate it anew. This is deeply uncool because terms that would
                --    normally be reduce-stopped may now get reduce-stopped once per level of sc recursion (potentially getting larger every time).
                --    FIXME: this is serious :-(
                (deeds', heap') = partiallyRebuildState state'
                spec_failed_xs = S.fromList [x' | Update x' <- map tagee k]
                spec_failed_h = h'_winners `restrict` spec_failed_xs
          = (stats `mappend` stats', deeds', heap', threaded_hist', IS.fromList [tg | hb <- M.elems spec_failed_h, Just tg <- [heapBindingTag hb]] `IS.union` losers', spec_failed_xs `S.union` speculated')
          | otherwise
          = (stats, deeds, Heap h'_winners ids, threaded_hist, losers, speculated)

    partiallyRebuildState :: State -> (Deeds, Heap)
    partiallyRebuildState (deeds, Heap h ids, k, (rn, qa)) = (deeds + annedSize e', Heap (h `M.union` h_updated) ids)
      where
        (h_updated, (_, e')) = rebuildStack k (renameIn (renameAnnedTerm ids) (rn, fmap qaToAnnedTerm' qa))
          
        rebuildStack []     e' = (M.empty, promote e')
        rebuildStack (kf:k) e' = case tagee kf of
            Apply x'                        -> rebuildStack k (annedTerm tg (e' `App` x'))
            Scrutinise in_alts              -> rebuildStack k (annedTerm tg (Case e' (renameIn (renameAnnedAlts ids) in_alts)))
            PrimApply pop in_anned_vs in_es -> rebuildStack k (annedTerm tg (PrimOp pop (map (fmap Value . renameIn (renameAnnedValue ids)) in_anned_vs ++ e' : map (renameIn (renameAnnedTerm ids)) in_es)))
            Update x'                       -> (M.insert x' (internallyBound (promote e')) h', in_e)
              where (h', in_e) = rebuildStack k (annedTerm tg (Var x'))
          where tg = tag kf
    
        promote :: AnnedTerm -> In AnnedTerm
        promote e' = (mkIdentityRenaming (S.toList (annedFreeVars e')), e')

reduce :: State -> (SCStats, State)
reduce orig_state = go (mkHistory (extra wQO)) orig_state
  where
    go hist state = case step state of
        Nothing -> (mempty, state)
        Just state' -> case terminate hist (state', state') of
          Continue hist'         -> go hist' state'
          Stop (_gen, old_state) -> trace "reduce-stop" $ (mempty { stat_reduce_stops = 1 }, if rEDUCE_ROLLBACK then old_state else state) -- TODO: generalise?


--
-- == The drive loop ==
--

data Promise f = P {
    fun        :: Var,         -- Name assigned in output program
    abstracted :: [Out Var],   -- Abstracted over these variables
    meaning    :: f State      -- Minimum adequate term. Nothing if this promise has been superceded by one with less free variables (this will only occur in the fulfilments)
  }

instance MonadStatics ScpM where
    bindCapturedFloats = bindFloats

-- Note [Floating h-functions past the let-bound variables to which they refer]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- This seems like a reasonable thing to do because some variables will become free after supercompilation.
-- However, there really isn't much point doing the float because I won't be able to tie back to the floated thing
-- in any other branch.
--
-- Indeed, allowing such tiebacks may be a source of bugs! Consider a term like:
--
--  x |-> <10>
--  x + 5
--
-- After supercompilation, we will have:
--
--  15
--
-- Since we check the *post supercompilation* free variables here, that h function could be floated
-- upwards, so it is visible to later supercompilations. But what if our context had looked like:
--
--   (let x = 10 in x + 5, let x = 11 in x + 5)
--
-- Since we only match phantoms by name, we are now in danger of tying back to this h-function when we
-- supercompile the second component of the pair!
--
-- Conclusion: don't bother with this rubbish.
--
-- Note [Variables reachable from let-bindings]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- TODO: we shouldn't lambda-abstract over any variables reachable via the let-bound thing. Doing so needlessly
-- passes them around via lambdas when they will always be available in the closure.
--
-- Consider this example:
--
--   \y -> let x = \z -> .. too big to inline ... y ...
---        in (... x ..., ... x ...)
--
-- When supercompliing each component of the pair we might feel tempted to generate h-functions lambda abstracted over
-- y, but doing so is pointless (just hides information from GHC) since the result will be trapped under the x binding anyway.
fulfilmentRefersTo :: FreeVars -> Fulfilment -> Maybe (Out Var)
fulfilmentRefersTo extra_statics (promise, e') = guard (Foldable.any (`S.member` extra_statics) (fvedTermFreeVars e' `S.union` extra_fvs)) >> return (fun promise)
  where
    -- We bind floats with phantoms bindings where those phantom bindings are bound.
    --
    -- For wrappers introduced by --refine-fvs, we still need to use (fvedTermFreeVars e') because that will include
    -- the wrapped h-function (e.g. the h83' wrapper for h83). This also applies (though more rarely) for non-wrappers
    -- because looking at the fvedTermFreeVars is the only way we can learn about what h-functions they require.
    extra_fvs = maybe S.empty stateLetBounders (meaning promise)

-- Used at the end of supercompilation to extract just those h functions that are actually referred to.
-- More often than not, this will be *all* the h functions, but if we don't discard h functions on rollback
-- then this is not necessarily the case!
fulfilmentReferredTo :: FreeVars -> Fulfilment -> Maybe FreeVars
fulfilmentReferredTo fvs (promise, e') = guard (fun promise `S.member` fvs) >> return (fvedTermFreeVars e')

-- We do need a fixed point here to identify the full set of h-functions to residualise.
-- The reason is that even if a static variable is not free in an output h-function, we might
-- have created (and make reference to) some h-function that *does* actually refer to one
-- of the static variables.
-- See also Note [Phantom variables and bindings introduced by scrutinisation]
partitionFulfilments :: (a -> fulfilment -> Maybe b)  -- ^ Decide whether a fulfilment should be residualised given our current a, returning a new b if so
                     -> ([b] -> a)                    -- ^ Combine bs of those fufilments being residualised into a new a
                     -> a                             -- ^ Used to decide whether the fufilments right here are suitable for residualisation
                     -> [fulfilment]                  -- ^ Fulfilments to partition
                     -> ([fulfilment], [fulfilment])  -- ^ Fulfilments that should be bound and those that should continue to float, respectively
partitionFulfilments p combine = go
  where go x fs -- | traceRender ("partitionFulfilments", x, map (fun . fst) fs) False = undefined
                | null fs_now' = ([], fs) 
                | otherwise    = first (fs_now' ++) $ go (combine xs') fs'
                where (unzip -> (fs_now', xs'), fs') = extractJusts (\fulfilment -> fmap (fulfilment,) $ p x fulfilment) fs

-- Note [Where to residualise fulfilments with FVs]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Be careful of this subtle problem:
--
--  let h6 = D[e1]
--      residual = ...
--      h7 = D[... let residual = ...
--                 in Just residual]
--  in ...
--
-- If we first drive e1 and create a fulfilment for the h6 promise, then when driving h7 we will eventually come across a residual binding for the
-- "residual" variable. If we aren't careful, we will notice that "residual" is a FV of the h6 fulfilment and residualise it deep within h7. But
-- what if the body of the outermost let drove to something referring to h6? We have a FV - disaster!
--
-- The right thing to do is to make sure that fulfilments created in different "branches" of the process tree aren't eligible for early binding in
-- that manner, but we still want to tie back to them if possible. The bindFloats function achieves this by carefully shuffling information between the
-- fulfilments and promises parts of the monadic-carried state.
bindFloats :: FreeVars -> ScpM a -> ScpM (Out [(Var, FVedTerm)], a)
bindFloats extra_statics mx
  = ScpM $ \e s k -> unScpM mx (e { promises = mapMaybe fulfilmentPromise (fulfilments s) ++ promises e, fulfilmentStack = (fulfilments s, extra_statics) : fulfilmentStack e }) (s { fulfilments = [] }) (kontinue e s k)
  where
    kontinue _e s k x s' = -- traceRender ("bindFloats", [(fun p, fvedTermFreeVars e) | (p, e) <- fs_now], [(fun p, fvedTermFreeVars e) | (p, e) <- fs_later]) $
                           k (fulfilmentsToBinds fs_now, x) (s' { fulfilments = fs_later ++ fulfilments s })
      where (fs_now, fs_later) = partitionFulfilments fulfilmentRefersTo S.fromList extra_statics (fulfilments s')

fulfilmentsToBinds :: [Fulfilment] -> Out [(Var, FVedTerm)]
fulfilmentsToBinds fs = sortBy (comparing ((read :: String -> Int) . dropLastWhile (== '\'') . drop 1 . name_string . fst)) [(fun p, e') | (p, e') <- fs]

freshHName :: ScpM Var
freshHName = ScpM $ \_e s k -> k (expectHead "freshHName" (names s)) (s { names = tail (names s) })

fulfilmentPromise :: Fulfilment -> Maybe (Promise Identity)
fulfilmentPromise (P fun abstracted (Just meaning), _) = Just (P fun abstracted (I meaning))
fulfilmentPromise _                                    = Nothing

getPromises :: ScpM [Promise Identity]
getPromises = ScpM $ \e s k -> k (mapMaybe fulfilmentPromise (fulfilments s) ++ promises e) s

getPromiseNames :: ScpM [Var]
getPromiseNames = ScpM $ \e s k -> k (map (fun . fst) (fulfilments s) ++ map fun (promises e)) s

promise :: Promise Identity -> ScpM (a, Out FVedTerm) -> ScpM (a, Out FVedTerm)
promise p opt = ScpM $ \e s k -> {- traceRender ("promise", fun p, abstracted p) $ -} unScpM (mx p) (e { promises = p : promises e, depth = 1 + depth e }) s k
  where
    mx p = do
      (a, e') <- opt
      -- We have a little trick here: we can reduce the number of free variables our "h" functions abstract over if we discover that after supercompilation some
      -- variables become dead. This lets us get some of the good stuff from absence analysis: we can actually reduce the number of loop-carried vars like this.
      -- It is particularly important to do this trick when we have unfoldings, because functions get a ton more free variables in that case.
      --
      -- If some of the fufilments we have already generated refer to us, we need to fix them up because their application sites will apply more arguments than we
      -- actually need. We aren't able to do anything about the stuff they spuriously allocate as a result, but we can make generate a little wrapper that just discards
      -- those arguments. With luck, GHC will inline it and good things will happen.
      --
      -- TODO: we can generate the wrappers in a smarter way now that we can always see all possible fulfilments?
      let fvs' = fvedTermFreeVars e'
          abstracted_set = S.fromList (abstracted p)
          abstracted'_set = fvs' `S.intersection` abstracted_set -- We still don't want to abstract over e.g. phantom bindings
          abstracted'_list = S.toList abstracted'_set
      ScpM $ \_e s k -> let fs' | abstracted_set == abstracted'_set || not rEFINE_FULFILMENT_FVS
                                 -- If the free variables are totally unchanged, there is nothing to be gained from clever fiddling
                                = (P { fun = fun p, abstracted = abstracted p, meaning = Just (unI (meaning p)) }, lambdas (abstracted p) e') : fulfilments s
                                | otherwise
                                 -- If the free variable set has got smaller, we can fulfill our old promise with a simple wrapper around a new one with fewer free variables
                                , let fun' = (fun p) { name_string = name_string (fun p) ++ "'" }
                                = (P { fun = fun p, abstracted = abstracted p, meaning = Nothing }, lambdas (abstracted p) (fvedTerm (Var fun') `apps` abstracted'_list)) :
                                  (P { fun = fun', abstracted = abstracted'_list, meaning = Just (unI (meaning p)) }, lambdas abstracted'_list e') : fulfilments s
                        in k () (s { fulfilments = fs' })
      
      fmap (((abstracted_set `S.union` stateLetBounders (unI (meaning p))) `S.union`) . S.fromList) getPromiseNames >>= \fvs -> assertRender ("sc: FVs", fun p, fvs' S.\\ fvs, fvs, e') (fvs' `S.isSubsetOf` fvs) $ return ()
      
      return (a, fun p `varApps` abstracted p)


data ScpEnv = ScpEnv {
    promises        :: [Promise Identity],
    fulfilmentStack :: [([Fulfilment], FreeVars)], -- Fulfilments at each level and the free variables of bindCapturedFloats that caused them to pushed.
                                                   -- We guarantee that promises for each these are already present in the promises field.
                                                   -- I have to store these in the monad-carried information because catchScpM has to be able to restore
                                                   -- (a subset of) them when rollback is initiated. See also Note [Where to residualise fulfilments with FVs]
    depth           :: Int
  }

type Fulfilment = (Promise Maybe, Out FVedTerm)

data ScpState = ScpState {
    names       :: [Var],
    fulfilments :: [Fulfilment], -- Fulfilments at the current level only
    stats       :: SCStats
  }

newtype ScpM a = ScpM { unScpM :: ScpEnv -> ScpState -> (a -> ScpState -> (SCStats, Out FVedTerm)) -> (SCStats, Out FVedTerm) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \_e s k -> k x s
    (!mx) >>= fxmy = ScpM $ \e s k -> unScpM mx e s (\x s -> unScpM (fxmy x) e s k)

runScpM :: ScpM (Out FVedTerm) -> (SCStats, Out FVedTerm)
runScpM me = unScpM me init_e init_s (\e' s -> (stats s, letRecSmart (fulfilmentsToBinds $ fst $ partitionFulfilments fulfilmentReferredTo S.unions (fvedTermFreeVars e') (fulfilments s)) e'))
  where
    init_e = ScpEnv { promises = [], fulfilmentStack = [], depth = 0 }
    init_s = ScpState { names = map (\i -> name $ 'h' : show (i :: Int)) [0..], fulfilments = [], stats = mempty }

catchScpM :: ((forall b. c -> ScpM b) -> ScpM a) -- ^ Action to try: supplies a function than can be called to "raise an exception". Raising an exception restores the original ScpEnv and ScpState
          -> (c -> ScpM a)                       -- ^ Handler deferred to if an exception is raised
          -> ScpM a                              -- ^ Result from either the main action or the handler
catchScpM f_try f_abort = ScpM $ \e s k -> unScpM (f_try (\c -> ScpM $ \e' s' _k' ->
    unScpM (f_abort c) e (if dISCARD_FULFILMENTS_ON_ROLLBACK
                          then s
                          else let not_completed = S.fromList (map fun (promises e')) S.\\ S.fromList (map fun (promises e))
                                   (fss_candidates, _fss_common) = splitByReverse (fulfilmentStack e) (fulfilmentStack e')
                                   
                                   -- Since we are rolling back we need to float as many of the fulfilments created in between here and the rollback point
                                   -- upwards. This means that we don't lose the work that we already did to supercompile those bindings.
                                   --
                                   -- The approach is to accumulate a set of floating fulfilments that I try to move past each statics set one at a time,
                                   -- from inside (deeper in the tree) to the outside (closer to top level).
                                   go fs_floating [] = fs_floating
                                   go fs_floating ((fs_candidates, extra_statics):fss_candidates) = go fs_ok fss_candidates
                                      where (_fs_discard, fs_ok) = partitionFulfilments fulfilmentRefersTo S.fromList (not_completed `S.union` extra_statics) (fs_candidates ++ fs_floating)
                               in s' { fulfilments = go [] fss_candidates ++ fulfilments s })
                         k)) e s k

addStats :: SCStats -> ScpM ()
addStats scstats = ScpM $ \_e s k -> k () (s { stats = stats s `mappend` scstats })


type RollbackScpM = Generaliser -> ScpM (Deeds, Out FVedTerm)

sc, sc' :: History (State, RollbackScpM) (Generaliser, RollbackScpM) -> State -> ScpM (Deeds, Out FVedTerm)
sc  hist = memo (sc' hist) . gc
sc' hist state = (\raise -> check raise) `catchScpM` \gen -> stop gen hist -- TODO: I want to use the original history here, but I think doing so leads to non-term as it contains rollbacks from "below us" (try DigitsOfE2)
  where
    check this_rb = case terminate hist (state, this_rb) of
                      Continue hist' -> continue hist'
                      Stop (gen, rb) -> maybe (stop gen hist) ($ gen) $ guard sC_ROLLBACK >> Just rb
    stop gen hist = do addStats $ mempty { stat_sc_stops = 1 }
                       trace "sc-stop" $ split gen (sc hist) state -- Keep the trace exactly here or it gets floated out by GHC
    continue hist = do traceRenderScpM ("reduce end", pPrintFullState state')
                       addStats stats
                       split generaliseNothing (sc hist) state'
      where (stats, state') = (if sPECULATION then speculate else id) reduce state -- TODO: experiment with doing admissability-generalisation on reduced terms. My suspicion is that it won't help, though (such terms are already stuck or non-stuck but loopy: throwing stuff away does not necessarily remove loopiness).

memo :: (State -> ScpM (Deeds, Out FVedTerm))
     ->  State -> ScpM (Deeds, Out FVedTerm)
memo opt state = do
    ps <- getPromises
    case [ (p, (releaseStateDeed state, fun p `varApps` tb_dynamic_vs))
         | p <- ps
         , Just rn_lr <- [-- (\res -> if isNothing res then traceRender ("no match:", fun p) res else res) $
                           match (unI (meaning p)) state]
          -- NB: because I can trim reduce the set of things abstracted over above, it's OK if the renaming derived from the meanings renames vars that aren't in the abstracted list, but NOT vice-versa
         , let bad_renames = S.fromList (abstracted p) S.\\ M.keysSet (unRenaming rn_lr) in assertRender (text "Renaming was inexhaustive:" <+> pPrint bad_renames $$ pPrint (fun p) $$ pPrintFullState (unI (meaning p)) $$ pPrint rn_lr $$ pPrintFullState state) (S.null bad_renames) True
         , let rn_fvs = map (safeRename ("tieback: FVs for " ++ render (pPrint (fun p) $$ text "Us:" $$ pPrint state $$ text "Them:" $$ pPrint (meaning p)))
                                        rn_lr) -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               tb_dynamic_vs = rn_fvs (abstracted p)
         ] of
      (_p, res):_ -> {- traceRender ("tieback", pPrintFullState state, fst res) $ -} do
        traceRenderScpM ("=sc", fun _p, pPrintFullState state, res)
        return res
      [] -> {- traceRender ("new drive", pPrintFullState state) $ -} do
        let vs = stateLambdaBounders state
        
        -- NB: promises are lexically scoped because they may refer to FVs
        x <- freshHName
        promise P { fun = x, abstracted = S.toList vs, meaning = I state } $ do
            traceRenderScpM (">sc", x, pPrintFullState state)
            res <- opt state
            traceRenderScpM ("<sc", x, pPrintFullState state, res)
            return res

traceRenderScpM :: Pretty a => a -> ScpM ()
traceRenderScpM x = ScpM (\e s k -> k (depth e) s) >>= \depth -> traceRenderM $ nest depth $ pPrint x
