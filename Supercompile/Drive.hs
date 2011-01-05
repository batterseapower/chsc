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

import qualified Data.Foldable as Foldable
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

reduce :: (Deeds, State) -> (Deeds, State)
reduce (deeds, orig_state) = go (mkHistory (extra wQO)) (deeds, orig_state)
  where
    go hist (deeds, state)
      -- | traceRender ("reduce.go", pPrintFullState state) False = undefined
      | not eVALUATE_PRIMOPS, (_, _, (_, annee -> PrimOp _ _)) <- state = (deeds, state)
      | otherwise = fromMaybe (deeds, state) $ either id id $ do
          hist' <- case terminate hist (state, (deeds, state)) of
                      _ | intermediate state  -> Right hist
                      -- _ | traceRender ("reduce.go (non-intermediate)", pPrintFullState state) False -> undefined
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
    fun        :: Var,             -- Name assigned in output program
    abstracted :: [Out Var],       -- Abstracted over these variables
    meaning    :: State            -- Minimum adequate term
  }

instance MonadStatics ScpM where
    bindCapturedFloats extra_statics mx = bindFloats (partition_fulfilments extra_statics) mx
      where
        -- We do need a fixed point here to identify the full set of h-functions to residualise.
        -- The reason is that even if a static variable is not free in an output h-function, we might
        -- have created (and make reference to) some h-function that *does* actually refer to one
        -- of the static variables.
        -- See also Note [Phantom variables and bindings introduced by scrutinisation]
        partition_fulfilments extra_statics fs
          | extra_statics == extra_statics' = (fs_now, fs_later)
          | otherwise                       = partition_fulfilments extra_statics' fs
          where
            (fs_now, fs_later)   = partition (Foldable.any (\x -> x `S.member` extra_statics) . fvedTermFreeVars . snd) fs
            extra_statics' = extra_statics `S.union` S.fromList (map (fun . fst) fs_now)

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
bindFloats :: ([Fulfilment] -> ([Fulfilment], [Fulfilment]))
           -> ScpM a -> ScpM (Out [(Var, FVedTerm)], a)
bindFloats partition_fulfilments mx
  = ScpM $ \e s k -> unScpM mx (e { promises = map fst (fulfilments s) ++ promises e }) (s { fulfilments = [] })
                               (\x _e (s'@(ScpState { fulfilments = (partition_fulfilments -> (fs_now, fs_later)) })) -> -- traceRender ("bindFloats", [(fun p, fvedTermFreeVars e) | (p, e) <- fs_now], [(fun p, fvedTermFreeVars e) | (p, e) <- fs_later]) $
                                                                                                                         k (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) [(fun p, e') | (p, e') <- fs_now], x)
                                                                                                                           e (s' { fulfilments = fs_later ++ fulfilments s }))

freshHName :: ScpM Var
freshHName = ScpM $ \e s k -> k (expectHead "freshHName" (names s)) e (s { names = tail (names s) })

getPromises :: ScpM [Promise]
getPromises = ScpM $ \e s k -> k (promises e ++ map fst (fulfilments s)) e s

promise :: Promise -> ScpM (a, Out FVedTerm) -> ScpM (a, Out FVedTerm)
promise p opt = ScpM $ \e s k -> {- traceRender ("promise", fun p, abstracted p) $ -} unScpM (mx p) (e { promises = p : promises e, depth = 1 + depth e }) s k
  where
    mx p = do
      (a, e') <- opt
      ScpM $ \e s k -> k () e (s { fulfilments = (p, lambdas (abstracted p) e') : fulfilments s })
      
      let fvs' = fvedTermFreeVars e' in fmap (((S.fromList (abstracted p) `S.union` stateStaticBinders (meaning p)) `S.union`) . S.fromList . map fun) getPromises >>= \fvs -> assertRender ("sc: FVs", fun p, fvs' S.\\ fvs, fvs, e') (fvs' `S.isSubsetOf` fvs) $ return ()
      
      return (a, fun p `varApps` abstracted p)


data ScpEnv = ScpEnv {
    promises :: [Promise],
    depth :: Int
  }

type Fulfilment = (Promise, Out FVedTerm)

data ScpState = ScpState {
    names       :: [Var],
    fulfilments :: [Fulfilment]
  }

newtype ScpM a = ScpM { unScpM :: ScpEnv -> ScpState -> (a -> ScpEnv -> ScpState -> Out FVedTerm) -> Out FVedTerm }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \e s k -> k x e s
    (!mx) >>= fxmy = ScpM $ \e s k -> unScpM mx e s (\x _e s -> unScpM (fxmy x) e s k)

runScpM :: ScpM (Out FVedTerm) -> Out FVedTerm
runScpM me = unScpM (bindFloats (\fs -> (fs, [])) me) init_e init_s (\(xes', e') _ _ -> letRecSmart xes' e')
  where
    init_e = ScpEnv { promises = [], depth = 0 }
    init_s = ScpState { names = map (\i -> name $ 'h' : show (i :: Int)) [0..], fulfilments = [] }

catchScpM :: ((forall b. c -> ScpM b) -> ScpM a) -- ^ Action to try: supplies a function than can be called to "raise an exception". Raising an exception restores the original ScpEnv and ScpState
          -> (c -> ScpM a)                       -- ^ Handler deferred to if an exception is raised
          -> ScpM a                              -- ^ Result from either the main action or the handler
catchScpM f_try f_abort = ScpM $ \e s k -> unScpM (f_try (\c -> ScpM $ \_ _ _ -> unScpM (f_abort c) e s k)) e s k


type RollbackScpM = Generaliser -> ScpM (Deeds, Out FVedTerm)

sc, sc' :: History (State, RollbackScpM) (Generaliser, RollbackScpM) -> (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
sc  hist = memo (sc' hist)
sc' hist (deeds, state) = (\raise -> check raise) `catchScpM` \gen -> stop gen hist -- TODO: I want to use the original history here, but I think doing so leads to non-term as it contains rollbacks from "below us" (try DigitsOfE2)
  where
    check this_rb = case terminate hist (state, this_rb) of
                      Continue hist' -> continue hist'
                      Stop (gen, rb) -> maybe (stop gen hist) ($ gen) $ guard sC_ROLLBACK >> Just rb
    stop gen hist = do traceRenderScpM "sc-stop"
                       split gen               (sc hist) (deeds,  state)
    continue hist = do traceRenderScpM ("reduce end", pPrintFullState state')
                       split generaliseNothing (sc hist) (deeds', state')
      where (deeds', state') = gc (reduce (deeds, state)) -- TODO: experiment with doing admissability-generalisation on reduced terms. My suspicion is that it won't help, though (such terms are already stuck or non-stuck but loopy: throwing stuff away does not necessarily remove loopiness).

memo :: ((Deeds, State) -> ScpM (Deeds, Out FVedTerm))
     ->  (Deeds, State) -> ScpM (Deeds, Out FVedTerm)
memo opt (deeds, state) = do
    ps <- getPromises
    case [ (p, (releaseStateDeed deeds state, fun p `varApps` tb_dynamic_vs))
         | p <- ps
         , Just rn_lr <- [-- (\res -> if isNothing res then traceRender ("no match:", fun p) res else res) $
                           match (meaning p) state]
         , let bad_renames = S.fromList (abstracted p) `symmetricDifference` M.keysSet (unRenaming rn_lr) in assertRender (text "Renaming was inexhaustive or too exhaustive:" <+> pPrint bad_renames $$ pPrint rn_lr $$ pPrintFullState state) (S.null bad_renames) True
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
        promise P { fun = x, abstracted = S.toList (vs S.\\ static_vs), meaning = state } $ do
            traceRenderScpM (">sc", x, pPrintFullState state, deeds)
            res <- opt (deeds, case state of (Heap h ids, k, in_e) -> (Heap (M.insert x Environmental h) ids, k, in_e)) -- TODO: should I just put "h" functions into a different set of statics??
            traceRenderScpM ("<sc", x, pPrintFullState state, res)
            return res

traceRenderScpM :: Pretty a => a -> ScpM ()
traceRenderScpM x = ScpM (\e s k -> k (depth e) e s) >>= \depth -> traceRenderM $ nest depth $ pPrint x
