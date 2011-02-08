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

import Evaluator.Evaluate
import Evaluator.FreeVars
import Evaluator.Residualise
import Evaluator.Syntax

import Size.Deeds

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
import Data.Tree


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
supercompile e = traceRender ("all input FVs", input_fvs) $ second (fVedTermToTerm . if pRETTIFY then prettify else id) $ runScpM $ liftM snd $ sc (mkHistory (extra wQO)) (deeds, state)
  where input_fvs = annedTermFreeVars anned_e
        (deeds, state) = normalise (mkDeeds (bLOAT_FACTOR - 1) (t, pPrint . rb), (Heap (setToMap Environmental input_fvs) reduceIdSupply, [], (mkIdentityRenaming $ S.toList input_fvs, anned_e)))
        anned_e = toAnnedTerm e
        
        (t, rb) = extractDeeds (\f e -> let (ts, rb) = f (annee e)
                                        in (Node (annedTag e) ts, \(Node unc ts') -> Counted unc (rb ts'))) anned_e
        
        extractDeeds :: (forall a b.    (a        -> ([Tree Tag], [Tree Int] -> b))
                                     -> Anned a   -> (Tree Tag,   Tree Int   -> Counted b))
                     -> AnnedTerm -> (Tree Tag, Tree Int -> CountedTerm)
        extractDeeds rec = term
          where 
            term = rec term'
            term' e = case e of
              Var x              -> ([], \[] -> Var x)
              Value (Indirect x) -> ([], \[] -> Value (Indirect x))
              Value (Lambda x e) -> ([t], \[t'] -> Value (Lambda x (rb t')))
                where (t, rb) = term e
              Value (Data dc xs) -> ([], \[] -> Value (Data dc xs))
              Value (Literal l)  -> ([], \[] -> Value (Literal l))
              App e x            -> ([t], \[t'] -> App (rb t') x)
                where (t, rb) = term e
              PrimOp pop es      -> (ts, \ts' -> PrimOp pop (zipWith ($) rbs ts'))
                where (ts, rbs) = unzip (map term es)
              Case e (unzip -> (alt_cons, alt_es)) -> (t : ts, \(t':ts') -> Case (rb t') (alt_cons `zip` zipWith ($) rbs ts'))
                where (t, rb)   = term e
                      (ts, rbs) = unzip (map term alt_es)
              LetRec (unzip -> (xs, es)) e         -> (t : ts, \(t':ts') -> LetRec (xs `zip` zipWith ($) rbs ts') (rb t'))
                where (t, rb)   = term e
                      (ts, rbs) = unzip (map term es)


--
-- == Bounded multi-step reduction ==
--

-- TODO: have the garbage collector collapse indirections to indirections (but unlike GHC, not further!)
-- TODO: have the garbage collector eliminate extra update frames
gc :: (Deeds, State) -> (Deeds, State)
gc (deeds, (Heap h ids, k, in_e)) = transitiveInline h (releasePureHeapDeeds deeds h, (Heap M.empty ids, k, in_e))
  where
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
    -- So I nixed in favour of a bit of gc in this module. TODO: experiment with not GCing here either.


type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


speculate :: ((Deeds, State) -> (SCStats, (Deeds, State)))
          -> (Deeds, State) -> (SCStats, (Deeds, State))
speculate reduce = snd . go (0 :: Int) (mkHistory wQO) (emptyLosers, S.empty)
  where
    go depth hist (losers, speculated) (deeds, state) = case terminate hist state of
        Continue hist' -> continue depth hist' (losers, speculated) (deeds, state)
        _              -> ((losers, speculated), (mempty, (deeds, state))) -- We MUST NOT EVER reduce in this branch or speculation will loop on e.g. infinite map
    
    continue depth hist (losers, speculated) (deeds, state) = ((losers', speculated'), (stats', (deeds'', (Heap (h'_winners' `M.union` h'_losers) ids'', k, in_e))))
      where
        (stats, (deeds', _state'@(Heap h' ids', k, in_e))) = reduce (deeds, state)
        
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
                                | otherwise           = M.partition (\hb -> maybe False (`IS.member` losers) (heapBindingTag_ hb)) h'
        
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
        (stats', deeds'', Heap h'_winners' ids'', losers', speculated') = M.foldrWithKey speculate_one (stats, deeds', Heap h'_winners ids', losers, speculated) h'_winners
        speculate_one x' hb (stats, deeds, Heap h'_winners ids, losers, speculated)
          -- | not (isValue (annee (snd in_e))), traceRender ("speculate", x', depth, pPrintFullUnnormalisedState (Heap (h {- `exclude` M.keysSet base_h -}) ids, k, in_e)) False = undefined
          | Just tg <- heapBindingTag_ hb
          , x' `S.notMember` speculated
          , let -- We're going to be a bit clever here: to speculate a heap binding, just put that variable into the focus and reduce the resulting term.
                -- The only complication occurs when comes back with a non-empty stack, in which case we need to deal with any unreduced update frames.
                ((losers', speculated'), (stats', (deeds', (Heap h' ids', k, _in_qa')))) = go (depth + 1) hist (losers, S.insert x' speculated) (normalise (deeds, (Heap h'_winners ids, [], (mkIdentityRenaming [x'], annedTerm tg (Var x')))))
                -- Update frames present in the output indicate a failed speculation attempt. (Though if a var is the focus without an update frame yet that is also failure of a sort...)
                -- We restore the original input bindings for such variables. We will also add them to the speculated set so we don't bother looking again. Note that this might make some heap
                -- bindings dead (because they are referred to by the overwritten terms), but we'll just live with that and have the GC clean it up later (pessimising deeds a bit, but never mind).
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
                -- What I do in this situation (failed_restore non-null) is to "agressively" roll back, discarding work done by the nested reduce and any things it added to the speculated set.
                -- Hopefully this case won't hit too often so it won't slow speculation down. (In fact, I think it only hits on the SimpleLaziness toy benchmark).
                -- 
                -- TODO: this is all very nasty
                spec_failed_xs = S.fromList [x' | Update x' <- map tagee k]
                h_restore = h'_winners `restrict` spec_failed_xs
                failed_restore = spec_failed_xs S.\\ M.keysSet h_restore
          -- , S.null failed_restore || trace (show (pPrint (x', failed_restore, spec_failed_xs, pPrintFullState _state', pPrintHeap (Heap h' ids'), pPrintHeap $ Heap h'_winners ids'))) True
          = if S.null failed_restore
            then (stats `mappend` stats', deeds', Heap (h_restore `M.union` h') ids', IS.fromList [tg | hb <- M.elems h_restore, Just tg <- [heapBindingTag_ hb]] `IS.union` losers', spec_failed_xs `S.union` speculated')
            else (stats `mappend` stats', deeds,  Heap h'_winners ids, losers', S.insert x' speculated)
          | otherwise
          = (stats, deeds, Heap h'_winners ids, losers, speculated)

reduce :: (Deeds, State) -> (SCStats, (Deeds, State))
reduce (deeds, orig_state) = go (mkHistory (extra wQO)) (deeds, orig_state)
  where
    go hist (deeds, state)
      -- | traceRender ("reduce.go", pPrintFullState state) False = undefined
      | otherwise = second (fromMaybe (deeds, state)) $ either (mempty { stat_reduce_stops = 1 },) (\mb_it -> maybe (mempty,Nothing) (second Just) mb_it) $ do
          hist' <- case terminate hist (state, (deeds, state)) of
                      _ | intermediate state  -> Right hist
                      -- _ | traceRender ("reduce.go (non-intermediate)", pPrintFullState state) False -> undefined
                      Continue hist               -> Right hist
                      Stop (_gen, (deeds, state)) -> trace "reduce-stop" $ Left (guard rEDUCE_ROLLBACK >> return (deeds, state)) -- TODO: generalise?
          Right $ fmap (go hist') $ step (deeds, state)
    
    intermediate :: State -> Bool
    intermediate (_, _, (_, annee -> Question _)) = False
    intermediate _ = True


--
-- == The drive loop ==
--

data Promise f = P {
    fun        :: Var,         -- Name assigned in output program
    abstracted :: [Out Var],   -- Abstracted over these variables
    meaning    :: f State      -- Minimum adequate term. Nothing if this promise has been superceded by one with less free variables (this will only occur in the fulfilments)
  }

instance MonadStatics ScpM where
    bindCapturedFloats extra_statics mx | dISCARD_FULFILMENTS_ON_ROLLBACK = bindFloats (\_ -> partitionFulfilments fulfilmentRefersTo S.fromList extra_statics) mx
                                        | otherwise                       = fmap ([],) mx -- NB: we can't use bindFloats or some fulfilments get lost when we roll back since they are hidden in the promises temporarily by bindFlotas

-- We would have a subtle bug here if (as in some branches) we let the evaluator look into
-- phantoms. Consider a term like:
--
--  x |-> <10>
--  x + 5
--
-- After supercompilation, we will have:
--
--  15
--
-- Since we check the *post supercompilation* free variables here, that h function will be floated
-- upwards, so it is visible to later supercompilations. But what if our context had looked like:
--
--   (let x = 10 in x + 5, let x = 11 in x + 5)
--
-- Since we only match phantoms by name, we are now in danger of tying back to this h-function when we
-- supercompile the second component of the pair!
--
-- I think this is responsible for the subtle bugs in some of the imaginary suite benchmarks (in particular,
-- integrate) that I saw on my phantom-lookthrough branches.
fulfilmentRefersTo :: FreeVars -> Fulfilment -> Maybe (Out Var)
fulfilmentRefersTo extra_statics (promise, e') = guard (Foldable.any (`S.member` extra_statics) (fvedTermFreeVars e')) >> return (fun promise)

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
partitionFulfilments :: (a -> Fulfilment -> Maybe b)  -- ^ Decide whether a fulfilment should be residualised given our current a, returning a new b if so
                     -> ([b] -> a)                    -- ^ Combine bs of those fufilments being residualised into a new a
                     -> a                             -- ^ Used to decide whether the fufilments right here are suitable for residualisation
                     -> [Fulfilment]                  -- ^ Fulfilments to partition
                     -> ([Fulfilment], [Fulfilment])  -- ^ Fulfilments that should be bound and those that should continue to float, respectively
partitionFulfilments p combine = go
  where go x fs -- | traceRender ("partitionFulfilments", x, map (fun . fst) fs) False = undefined
                | null fs_now' = ([], fs) 
                | otherwise    = first (fs_now' ++) $ go (combine xs') fs'
                where (unzip -> (fs_now', xs'), fs') = extractJusts (\fulfilment -> fmap (fulfilment,) $ p x fulfilment) fs

-- NB: be careful of this subtle problem:
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
bindFloats :: (a -> [Fulfilment] -> ([Fulfilment], [Fulfilment]))
           -> ScpM a -> ScpM (Out [(Var, FVedTerm)], a)
bindFloats partition_floats mx
  = ScpM $ \e s k -> unScpM mx (e { promises = mapMaybe fulfilmentPromise (fulfilments s) ++ promises e }) (s { fulfilments = [] })
                               (\x (s'@(ScpState { fulfilments = (partition_floats x -> (fs_now, fs_later)) })) -> -- traceRender ("bindFloats", [(fun p, fvedTermFreeVars e) | (p, e) <- fs_now], [(fun p, fvedTermFreeVars e) | (p, e) <- fs_later]) $
                                                                                                                   k (sortBy (comparing ((read :: String -> Int) . dropLastWhile (== '\'') . drop 1 . name_string . fst)) [(fun p, e') | (p, e') <- fs_now], x)
                                                                                                                     (s' { fulfilments = fs_later ++ fulfilments s }))

freshHName :: ScpM Var
freshHName = ScpM $ \_e s k -> k (expectHead "freshHName" (names s)) (s { names = tail (names s) })

fulfilmentPromise :: Fulfilment -> Maybe (Promise Identity)
fulfilmentPromise (P fun abstracted (Just meaning), _) = Just (P fun abstracted (I meaning))
fulfilmentPromise _                                    = Nothing

getPromises :: ScpM [Promise Identity]
getPromises = ScpM $ \e s k -> k (promises e ++ mapMaybe fulfilmentPromise (fulfilments s)) s

getPromiseNames :: ScpM [Var]
getPromiseNames = ScpM $ \e s k -> k (map fun (promises e) ++ [fun p | (p, _) <- fulfilments s]) s

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
      
      fmap (((S.fromList (abstracted p) `S.union` stateStaticBinders (unI (meaning p))) `S.union`) . S.fromList) getPromiseNames >>= \fvs -> assertRender ("sc: FVs", fun p, fvs' S.\\ fvs, fvs, e') (fvs' `S.isSubsetOf` fvs) $ return ()
      
      return (a, fun p `varApps` abstracted p)


data ScpEnv = ScpEnv {
    promises :: [Promise Identity],
    depth :: Int
  }

type Fulfilment = (Promise Maybe, Out FVedTerm)

data ScpState = ScpState {
    names       :: [Var],
    fulfilments :: [Fulfilment],
    stats       :: SCStats
  }

newtype ScpM a = ScpM { unScpM :: ScpEnv -> ScpState -> (a -> ScpState -> (SCStats, Out FVedTerm)) -> (SCStats, Out FVedTerm) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \_e s k -> k x s
    (!mx) >>= fxmy = ScpM $ \e s k -> unScpM mx e s (\x s -> unScpM (fxmy x) e s k)

runScpM :: ScpM (Out FVedTerm) -> (SCStats, Out FVedTerm)
runScpM me = unScpM (bindFloats (\e' -> partitionFulfilments fulfilmentReferredTo S.unions (fvedTermFreeVars e')) me) init_e init_s (\(xes', e') s -> (stats s, letRecSmart xes' e'))
  where
    init_e = ScpEnv { promises = [], depth = 0 }
    init_s = ScpState { names = map (\i -> name $ 'h' : show (i :: Int)) [0..], fulfilments = [], stats = mempty }

catchScpM :: ((forall b. c -> ScpM b) -> ScpM a) -- ^ Action to try: supplies a function than can be called to "raise an exception". Raising an exception restores the original ScpEnv and ScpState
          -> (c -> ScpM a)                       -- ^ Handler deferred to if an exception is raised
          -> ScpM a                              -- ^ Result from either the main action or the handler
catchScpM f_try f_abort = ScpM $ \e s k -> unScpM (f_try (\c -> ScpM $ \e' s' _k' ->
    unScpM (f_abort c) e (if dISCARD_FULFILMENTS_ON_ROLLBACK
                          then s
                          else let not_completed = S.fromList (map fun (promises e')) S.\\ S.fromList (map fun (promises e))
                                   (_fs_discard, fs_ok) = partitionFulfilments fulfilmentRefersTo S.fromList not_completed (fulfilments s')
                               in s' { fulfilments = fs_ok })
                         k)) e s k

addStats :: SCStats -> ScpM ()
addStats scstats = ScpM $ \_e s k -> k () (s { stats = stats s `mappend` scstats })


type RollbackScpM = Generaliser -> ScpM (Deeds, Out FVedTerm)

sc, sc' :: History (State, RollbackScpM) (Generaliser, RollbackScpM) -> (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
sc  hist = memo (sc' hist)
sc' hist (deeds, state) = (\raise -> check raise) `catchScpM` \gen -> stop gen hist -- TODO: I want to use the original history here, but I think doing so leads to non-term as it contains rollbacks from "below us" (try DigitsOfE2)
  where
    check this_rb = case terminate hist (state, this_rb) of
                      Continue hist' -> continue hist'
                      Stop (gen, rb) -> maybe (stop gen hist) ($ gen) $ guard sC_ROLLBACK >> Just rb
    stop gen hist = do addStats $ mempty { stat_sc_stops = 1 }
                       trace "sc-stop" $ split gen (sc hist) (deeds,  state) -- Keep the trace exactly here or it gets floated out by GHC
    continue hist = do traceRenderScpM ("reduce end", pPrintFullState state')
                       addStats stats
                       split generaliseNothing (sc hist) (deeds', state')
      where (stats, (deeds', state')) = second gc ((if sPECULATION then speculate else id) reduce (deeds, state)) -- TODO: experiment with doing admissability-generalisation on reduced terms. My suspicion is that it won't help, though (such terms are already stuck or non-stuck but loopy: throwing stuff away does not necessarily remove loopiness).

memo :: ((Deeds, State) -> ScpM (Deeds, Out FVedTerm))
     ->  (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
memo opt (deeds, state) = do
    ps <- getPromises
    case [ (p, (releaseStateDeed deeds state, fun p `varApps` tb_dynamic_vs))
         | p <- ps
         , Just rn_lr <- [-- (\res -> if isNothing res then traceRender ("no match:", fun p) res else res) $
                           match (unI (meaning p)) state]
          -- NB: because I can trim reduce the set of things abstracted over above, it's OK if the renaming derived from the meanings renames vars that aren't in the abstracted list, but NOT vice-versa
         , let bad_renames = S.fromList (abstracted p) S.\\ M.keysSet (unRenaming rn_lr) in assertRender (text "Renaming was inexhaustive:" <+> pPrint bad_renames $$ pPrint rn_lr $$ pPrintFullState state) (S.null bad_renames) True
         , let rn_fvs = map (safeRename ("tieback: FVs for " ++ render (pPrint (fun p) $$ text "Us:" $$ pPrint state $$ text "Them:" $$ pPrint (meaning p)))
                                        rn_lr) -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               tb_dynamic_vs = rn_fvs (abstracted p)
         ] of
      (_p, res):_ -> {- traceRender ("tieback", pPrintFullState state, fst res) $ -} do
        traceRenderScpM ("=sc", fun _p, pPrintFullState state, deeds, res)
        return res
      [] -> {- traceRender ("new drive", pPrintFullState state) $ -} do
        let (static_vs, vs) = stateStaticBindersAndFreeVars state
        
        -- NB: promises are lexically scoped because they may refer to FVs
        x <- freshHName
        promise P { fun = x, abstracted = S.toList (vs S.\\ static_vs), meaning = I state } $ do
            traceRenderScpM (">sc", x, pPrintFullState state, deeds)
            res <- opt (deeds, case state of (Heap h ids, k, in_e) -> (Heap (M.insert x Environmental h) ids, k, in_e)) -- TODO: should I just put "h" functions into a different set of statics??
            traceRenderScpM ("<sc", x, pPrintFullState state, res)
            return res

traceRenderScpM :: Pretty a => a -> ScpM ()
traceRenderScpM x = ScpM (\e s k -> k (depth e) s) >>= \depth -> traceRenderM $ nest depth $ pPrint x
