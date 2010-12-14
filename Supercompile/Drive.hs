{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards, BangPatterns, RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Drive (supercompile) where

import Supercompile.Match
import Supercompile.Split

import Core.FreeVars
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

import Algebra.Lattice

import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S
import qualified Data.IntSet as IS
import Data.Tree


wQO :: WQO State Generaliser
wQO | not tERMINATION_CHECK                        = postcomp (const generaliseNothing) unsafeNever
    | otherwise = case tAG_COLLECTION of TagBag   -> embedWithTagBags
                                         TagGraph -> embedWithTagGraphs
                                         TagSet   -> embedWithTagSets

supercompile :: Term -> Term
supercompile e = traceRender ("all input FVs", input_fvs) $ fVedTermToTerm $ runScpM $ fmap snd $ sc (mkHistory (extra wQO)) (deeds, state)
  where input_fvs = annedTermFreeVars anned_e
        state = (Heap (setToMap Environmental input_fvs) reduceIdSupply, [], (mkIdentityRenaming $ S.toList input_fvs, anned_e))
        anned_e = toAnnedTerm e
        
        deeds = mkDeeds (bLOAT_FACTOR - 1) (t, pPrint . rb)
        
        (t, rb) = extractDeeds (\f e -> let (ts, rb) = f (annee e)
                                        in (Node (annedTag e) ts, \(Node unc ts') -> Counted unc (rb ts'))) anned_e
        
        extractDeeds :: (forall a b.    (a        -> ([Tree Tag], [Tree Int] -> b))
                                     -> Anned a   -> (Tree Tag,   Tree Int   -> Counted b))
                     -> AnnedTerm -> (Tree Tag, Tree Int -> CountedTerm)
        extractDeeds rec = term
          where 
            var = rec var'
            var' x = ([], \[] -> x)
            
            term = rec term'
            term' e = case e of
              Var x              -> ([], \[] -> Var x)
              Value (Lambda x e) -> ([t], \[t'] -> Value (Lambda x (rb t')))
                where (t, rb) = term e
              Value (Data dc xs) -> ([], \[] -> Value (Data dc xs))
              Value (Literal l)  -> ([], \[] -> Value (Literal l))
              App e x            -> ([t1, t2], \[t1', t2'] -> App (rb1 t1') (rb2 t2'))
                where (t1, rb1) = term e
                      (t2, rb2) = var x
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
gc :: (Deeds, State) -> (Deeds, State)
gc (deeds, (Heap h ids, k, in_e)) = (M.fold (flip releaseHeapBindingDeeds) deeds h_dead,
                                     (Heap h_reachable ids, k, in_e))
  where
    (h_dead, h_reachable) = M.mapEitherWithKey (\x' hb -> maybe (Left hb) (\why_live -> Right $ demoteHeapBinding why_live hb) (x' `whyLive` reachable)) h
    reachable = lfpFrom (mkConcreteLiveness $ snd $ stackOpenFreeVars k $ inFreeVars annedTermFreeVars in_e) go
    go live = M.foldWithKey (\x' hb live -> maybe live (\why_live -> live `plusLiveness` heapBindingLiveness (demoteHeapBinding why_live hb)) (x' `whyLive` live)) live h
    
    -- TODO: fix this comment. It used to be attached to the update frame logic in the evaluator.
    --
    -- If we can GC the update frame (because it can't be referred to in the continuation) then:
    --  1) We don't have to actually update the heap or even claim a new deed
    --  2) We make the supercompiler less likely to terminate, because doing so tends to reduce TagBag sizes
    --
    -- NB: to prevent incorrectly garbage collecting bindings from the enclosing heap when we have speculation on,
    -- we pass around an extra "live set" of parts of the heap that might be referred to later on
    --
    -- TODO: make finding FVs much cheaper (i.e. memoise it in the syntax functor construction)
    -- TODO: could GC cycles as well (i.e. don't consider stuff from the Heap that was only referred to by the thing being removed as "GC roots")

speculate :: ((Deeds, State) -> (Deeds, State))
          -> (Deeds, State) -> (Deeds, State)
speculate reduce = snd . go (0 :: Int) (mkHistory wQO) emptyLosers
  where
    go depth hist losers (deeds, state) = case terminate hist state of
        Continue hist' | sPECULATION -> continue depth hist' losers (deeds, state)
        _                            -> (losers, (deeds, state))
    
    continue depth hist losers (deeds, state@(Heap h _, _, _)) = (losers', (deeds'', (Heap (h'_winners' `M.union` h'_losers) ids'', k, in_e)))
      where
        (deeds', (Heap h' ids', k, in_e)) = reduce (deeds, state)
        
        -- It is *very important* that we prevent speculation from forcing heap-carried things that have proved
        -- to be losers in the past. This prevents us discovering speculation failure of some head binding, and
        -- then forcing several thunks that are each strict in it. This change was motivated by DigitsOfE2 -- it
        -- speeds up supercompilation of that benchmark massively.
        (h'_losers, h'_winners) | sPECULATE_ON_LOSERS = (M.empty, h')
                                | otherwise           = M.partition (\hb -> maybe False (`IS.member` losers) (heapBindingTag hb)) h'
        
        -- NB: It is important that we accumulate losers across "go" invocations in a state-monady kind of way, or DigitsOfE2 blows out
        -- even more than normal (it still takes 22s with this change).
        -- TODO: I suspect we should accumulate Losers across the boundary of speculate as well
        -- TODO: there is a difference between losers due to termination-halting and losers because we didn't have neough
        -- information available to complete evaluation
        (deeds'', Heap h'_winners' ids'', losers') = M.foldWithKey speculate_one (deeds', Heap h'_winners ids', losers) (h'_winners M.\\ h)
        speculate_one x' (Concrete in_e) (deeds, Heap h'_winners ids, losers)
          -- | not (isValue (annee (snd in_e))), traceRender ("speculate", depth, residualiseState (Heap (h {- `exclude` M.keysSet base_h -}) ids, k, in_e)) False = undefined
          | otherwise = case (go (depth + 1) hist losers) (deeds, (Heap (M.delete x' h'_winners) ids, [], in_e)) of
            (losers', (deeds', (Heap h' ids', [], in_e'@(_, annee -> Value _)))) -> (deeds', Heap (M.insert x' (Concrete in_e') h')         ids', losers')
            (losers', _)                                                         -> (deeds,  Heap (M.insert x' (Concrete in_e)  h'_winners) ids,  IS.insert (annedTag (snd in_e)) losers')
        speculate_one x' hb              (deeds, Heap h'_winners ids, losers) 
          = (deeds, Heap (M.insert x' hb h'_winners) ids, losers)

reduce :: (Deeds, State) -> (Deeds, State)
reduce (deeds, orig_state) = go (mkHistory (extra wQO)) (deeds, orig_state)
  where
    go hist (deeds, state)
      -- | traceRender ("reduce.go", residualiseState state) False = undefined
      | not eVALUATE_PRIMOPS, (_, _, (_, annee -> PrimOp _ _)) <- state = (deeds, state)
      | otherwise = fromMaybe (deeds, state) $ either id id $ do
          hist' <- case terminate hist (state, (deeds, state)) of
                      _ | intermediate state  -> Right hist
                      -- _ | traceRender ("reduce.go (non-intermediate)", residualiseState state) False -> undefined
                      Continue hist               -> Right hist
                      Stop (_gen, (deeds, state)) -> trace "reduce-stop" $ Left (guard rEDUCE_ROLLBACK >> return (deeds, state)) -- TODO: generalise?
          Right $ fmap (go hist') $ step (deeds, state)
    
    intermediate :: State -> Bool
    intermediate (_, _, (_, annee -> Var _)) = False
    intermediate _ = True


--
-- == The drive loop ==
--

data Promise = P {
    fun        :: Var,       -- Name assigned in output program
    abstracted :: [Out Var], -- Abstracted over these variables
    lexical    :: [Out Var], -- Refers to these variables lexically (i.e. not via a lambda)
    meaning    :: State      -- Minimum adequate term
  }

-- Note [Which h functions to residualise in withStatics]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Imagine we have driven to this situation:
--
--  let map = ...
--  in ...
--
-- With these "h" functions floating out:
--
--  h1 = \fvs1 -> ... map ...
--  h2 = \fvs2 -> let map = ...
--                in ... h1 ...
--
-- Previously, what withStatics did was residualise those floating "h" function that have lexical
-- free variables that intersect with the set of statics (which is just {map} in this case).
--
-- However, this is insufficient in this example, because we built a map binding locally within h2
-- and so it does not occur as a lexical FV of h2. However, h2 refers to h1 (which does have map as a
-- lexical FV) so what is going to happen is that h2 will float out past h1 and we will get a variable
-- out of scope error at the reference to h1.
--
-- There are two solutions:
--  1) When pushing heap bindings down into several different contexts, give them different names in each
--     context. Then we will end up in a situation like:
--
--  let map1 = ...
--  in ...
--
--  h1 = \fvs1 -> ... map1 ...
--  h2 = \fvs2 -> let map2 = ...
--                in ... h1 ...
--
-- Now map1 will be a lexical FV of h1 and all will be well.
--
--  2) Make the h functions that get called into lexical FVs of the h function making the call, and then
--     compute the least fixed point of the statics set in withStatics, residualising h functions that are
--     referred to only by other h functions.
--
--  This solution is rather elegant because it falls out naturally if I make the FreeVars set returned by the
--  supercompiler exactly equal to the free variables of the term returned (previously I excluded h functions
--  from the set, but *included* lexical FVs of any h functions called). This simplifies the description of the
--  supercompiler but also means that in the future I might just be able to return a TermWithFVs or something --
--  memoising the FVs on the term structure itself.

instance MonadStatics ScpM where
     -- NB: it's important we still use bindFloats if (not lOCAL_TIEBACKS) because h functions are static
    bindCapturedFloats extra_statics mx = bindFloats (any (\x -> x `S.member` extra_statics) . lexical) mx

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
bindFloats :: (Promise -> Bool) -> ScpM a -> ScpM (Out [(Var, FVedTerm)], a)
bindFloats p mx = ScpM $ \e s k -> unScpM mx (e { promises = map fst (fulfilments s) ++ promises e }) (s { fulfilments = [] })
                                             (\x _e (s'@(ScpState { fulfilments = (partition (p . fst) -> (fs_now, fs_later)) })) -> -- traceRender ("bindFloats", [(fun p, lexical p, fvedTermFreeVars e) | (p, e) <- fs_now], [(fun p, lexical p, fvedTermFreeVars e) | (p, e) <- fs_later]) $
                                                                                                                                     k (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) [(fun p, lambdas (abstracted p) e') | (p, e') <- fs_now], x)
                                                                                                                                       e (s' { fulfilments = fs_later ++ fulfilments s }))

freshHName :: ScpM Var
freshHName = ScpM $ \e s k -> k (expectHead "freshHName" (names s)) e (s { names = tail (names s) })

getPromises :: ScpM [Promise]
getPromises = ScpM $ \e s k -> k (promises e ++ map fst (fulfilments s)) e s

promise :: Promise -> ScpM (a, Out FVedTerm) -> ScpM (a, Out FVedTerm)
promise p opt = ScpM $ \e s k -> traceRender ("promise", fun p, abstracted p, lexical p) $ unScpM (mx p) (e { promises = p : promises e }) s k
  where
    mx p = do
      (a, e') <- opt
      ScpM $ \e s k -> k () e (s { fulfilments = (p, e') : fulfilments s })
      
      let fvs' = fvedTermFreeVars e' in fmap (S.fromList . ((abstracted p ++ lexical p) ++) . map fun) getPromises >>= \fvs -> assertRender ("sc: FVs", fun p, fvs' S.\\ fvs, fvs) (fvs' `S.isSubsetOf` fvs) $ return ()
      
      return (a, fun p `varApps` abstracted p)


data ScpEnv = ScpEnv {
    promises :: [Promise]
  }

data ScpState = ScpState {
    names       :: [Var],
    fulfilments :: [(Promise, Out FVedTerm)]
  }

newtype ScpM a = ScpM { unScpM :: ScpEnv -> ScpState -> (a -> ScpEnv -> ScpState -> Out FVedTerm) -> Out FVedTerm }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \e s k -> k x e s
    (!mx) >>= fxmy = ScpM $ \e s k -> unScpM mx e s (\x _e s -> unScpM (fxmy x) e s k)

runScpM :: ScpM (Out FVedTerm) -> Out FVedTerm
runScpM me = unScpM (bindFloats (\_ -> True) me) init_e init_s (\(xes', e') _ _ -> letRecSmart xes' e')
  where
    init_e = ScpEnv { promises = [] }
    init_s = ScpState { names = map (\i -> name $ 'h' : show (i :: Int)) [0..], fulfilments = [] }

catchScpM :: ((forall b. c -> ScpM b) -> ScpM a) -- ^ Action to try: supplies a function than can be called to "raise an exception". Raising an exception restores the original ScpEnv and ScpState
          -> (c -> ScpM a)                       -- ^ Handler deferred to if an exception is raised
          -> ScpM a                              -- ^ Result from either the main action or the handler
catchScpM f_try f_abort = ScpM $ \e s k -> unScpM (f_try (\c -> ScpM $ \_ _ _ -> unScpM (f_abort c) e s k)) e s k


newtype SCRollback = SCRB { rollbackWith :: Generaliser -> ScpM (Deeds, Out FVedTerm) }

sc, sc' :: History (State, SCRollback) (Generaliser, SCRollback) -> (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
sc  hist = memo (sc' hist)
sc' hist (deeds, state) = (\raise -> check (SCRB raise)) `catchScpM` \gen -> stop gen hist -- TODO: I want to use the original history here, but I think doing so leads to non-term as it contains rollbacks from "below us" (try DigitsOfE2)
  where
    check mb_rb = case terminate hist (state, mb_rb) of
                    Continue hist' -> continue hist'
                    Stop (gen, rb) -> maybe (stop gen hist) (`rollbackWith` gen) $ guard sC_ROLLBACK >> Just rb
    stop gen hist = trace "sc-stop" $ split gen               (sc hist) (deeds, state)
    continue hist =                   split generaliseNothing (sc hist) ((\res@(_, state') -> traceRender ("reduce end", residualiseState state') res) $
                                                                         gc (speculate reduce (deeds, state))) -- TODO: experiment with doing admissability-generalisation on reduced terms. My suspicion is that it won't help, though (such terms are already stuck or non-stuck but loopy: throwing stuff away does not necessarily remove loopiness).

memo :: ((Deeds, State) -> ScpM (Deeds, Out FVedTerm))
     ->  (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
memo opt (deeds, state) = do
    ps <- getPromises
    case [ (p, (releaseStateDeed deeds state, fun p `varApps` tb_dynamic_vs))
         | p <- ps
         , Just rn_lr <- [-- (\res -> if isNothing res then traceRender ("no match:", fun p) res else res) $
                           match (meaning p) state]
         , let bad_renames = S.fromList (abstracted p) `symmetricDifference` M.keysSet (unRenaming rn_lr) in assertRender (text "Renaming was inexhaustive or too exhaustive:" <+> pPrint bad_renames $$ pPrint rn_lr $$ pPrint (residualiseState state) $$ case state of (Heap h _, _, _) -> pPrint (M.filter heapBindingNonConcrete h)) (S.null bad_renames) True
         , let rn_fvs = map (safeRename ("tieback: FVs for " ++ render (pPrint (fun p) $$ text "Us:" $$ pPrint state $$ text "Them:" $$ pPrint (meaning p)))
                                        rn_lr) -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               tb_dynamic_vs = rn_fvs (abstracted p)
         ] of
      (_p, res):_ -> {- traceRender ("tieback", residualiseState state, fst res) $ -} do
        traceRenderM ("=sc", fun _p, residualiseState state, deeds, res)
        return res
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        let (static_vs, vs) = stateStaticBindersAndFreeVars state
    
        -- NB: promises are lexically scoped because they may refer to FVs
        x <- freshHName
        promise P { fun = x, abstracted = S.toList (vs S.\\ static_vs), lexical = S.toList static_vs, meaning = state } $ do
            traceRenderM (">sc", x, residualiseState state, case state of (Heap h _, _, _) -> M.filter heapBindingNonConcrete h, deeds)
            res <- opt (deeds, case state of (Heap h ids, k, in_e) -> (Heap (M.insert x Environmental h) ids, k, in_e)) -- TODO: should I just put "h" functions into a different set of statics??
            traceRenderM ("<sc", x, residualiseState state, res)
            return res
