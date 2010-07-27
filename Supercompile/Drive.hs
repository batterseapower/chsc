{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards, BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Drive (supercompile) where

import Supercompile.Match
import Supercompile.Residualise
import Supercompile.Split

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Evaluator.Evaluate
import Evaluator.FreeVars
import Evaluator.Syntax

import Size.Deeds

import Termination.Terminate

import Name
import Renaming
import StaticFlags
import Utilities

import Control.Monad.Fix

import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S
import Data.Tree


supercompile :: Term -> Term
supercompile e = traceRender ("all input FVs", input_fvs) $ runScpM input_fvs $ fmap thd3 $ sc [] (deeds, state)
  where input_fvs = termFreeVars e
        state = (Heap M.empty reduceIdSupply, [], (mkIdentityRenaming $ S.toList input_fvs, tagged_e))
        tagged_e = tagTerm tagIdSupply e
        
        (t, rb) = extractDeeds tagged_e
        deeds = mkDeeds (bLOAT_FACTOR - 1) (t, pPrint . rb)
        extractDeeds (Tagged tg e) = -- traceRender ("extractDeeds", rb (fmap (fmap (const 1)) ts)) $
                                     (Node tg ts, \(Node unc ts') -> Counted unc (rb ts'))
          where (ts, rb) = extractDeeds' e
        extractDeeds' e = case e of
          Var x              -> ([], \[] -> Var x)
          Value (Lambda x e) -> ([t], \[t'] -> Value (Lambda x (rb t')))
            where (t, rb) = extractDeeds e
          Value (Data dc xs) -> ([], \[] -> Value (Data dc xs))
          Value (Literal l)  -> ([], \[] -> Value (Literal l))
          App e x            -> ([t1, t2], \[t1', t2'] -> App (rb1 t1') (rb2 t2'))
            where (t1, rb1) = extractDeeds e
                  (t2, rb2) = (Node (tag x) [], \(Node unc []) -> Counted unc (tagee x))
          PrimOp pop es      -> (ts, \ts' -> PrimOp pop (zipWith ($) rbs ts'))
            where (ts, rbs) = unzip (map extractDeeds es)
          Case e (unzip -> (alt_cons, alt_es)) -> (t : ts, \(t':ts') -> Case (rb t') (alt_cons `zip` zipWith ($) rbs ts'))
            where (t, rb)   = extractDeeds e
                  (ts, rbs) = unzip (map extractDeeds alt_es)
          LetRec (unzip -> (xs, es)) e         -> (t : ts, \(t':ts') -> LetRec (xs `zip` zipWith ($) rbs ts') (rb t'))
            where (t, rb)   = extractDeeds e
                  (ts, rbs) = unzip (map extractDeeds es)


--
-- == Termination ==
--

-- Other functions:
--  Termination.Terminate.terminate

-- This family of functions is the whole reason that I have to thread Tag information throughout the rest of the code:

stateTagBag :: State -> TagBag
stateTagBag (Heap h _, k, (_, e)) = pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` taggedTermTagBag e

pureHeapTagBag :: PureHeap -> TagBag
pureHeapTagBag = plusTagBags . map (taggedTagBag 5 . snd) . M.elems

stackTagBag :: Stack -> TagBag
stackTagBag = plusTagBags . map (tagTagBag 3) . concatMap stackFrameTags

taggedTermTagBag :: TaggedTerm -> TagBag
taggedTermTagBag = taggedTagBag 2

taggedTagBag :: Int -> Tagged a -> TagBag
taggedTagBag cls = tagTagBag cls . tag

tagTagBag :: Int -> Tag -> TagBag
tagTagBag cls = mkTagBag . return . injectTag cls


--
-- == Bounded multi-step reduction ==
--

reduce :: (Deeds, State) -> (Deeds, State)
reduce = go emptyHistory
  where
    go hist (deeds, state)
      | traceRender ("reduce.go", deeds, residualiseState state) False = undefined
      | not eVALUATE_PRIMOPS, (_, _, (_, Tagged _ (PrimOp _ _))) <- state = (deeds, state)
      | otherwise = case step (deeds, state) of
        Nothing -> (deeds, state)
        Just (deeds', state')
          | intermediate state' -> go hist (deeds', state')
          | otherwise           -> case terminate hist (stateTagBag state') of
              Stop           -> (deeds', state')
              Continue hist' -> go hist' (deeds', state')
    
    intermediate :: State -> Bool
    intermediate (_, _, (_, Tagged _ (Var _))) = False
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

instance MonadStatics ScpM where
    withStatics xs mx = bindFloats (\p -> any (`S.member` xs) (lexical p)) $ ScpM $ \e s -> (\(!res) -> traceRender ("withStatics", xs) res) $ unScpM mx (e { statics = statics e `S.union` xs }) s

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
-- fulfulmints and promises parts of the monadic-carried state.
bindFloats :: (Promise -> Bool) -> ScpM a -> ScpM ([(Out Var, Out Term)], a)
bindFloats p mx = ScpM $ \e s -> case unScpM mx (e { promises = map fst (fulfilments s) ++ promises e }) (s { fulfilments = [] }) of (s'@(ScpState { fulfilments = (partition (p . fst) -> (fs_now, fs_later)) }), x) -> traceRender ("bindFloats", map (fun . fst) fs_now, map (fun . fst) fs_later) $ (s' { fulfilments = fs_later ++ fulfilments s }, (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) [(fun p, lambdas (abstracted p) e') | (p, e') <- fs_now], x))

getStatics :: ScpM FreeVars
getStatics = ScpM $ \e s -> (s, statics e)

freshHName :: ScpM Var
freshHName = ScpM $ \_ s -> (s { names = tail (names s) }, expectHead "freshHName" (names s))

getPromises :: ScpM [Promise]
getPromises = ScpM $ \e s -> (s, promises e ++ map fst (fulfilments s))

promise :: (Name -> Promise) -> ScpM (a, b, Out Term) -> ScpM (a, b, Out Term)
promise mk_p opt = do
    x <- freshHName
    let p = mk_p x
    ScpM $ \e s -> traceRender ("promise", x) $ unScpM (mx p) e { promises = p : promises e } s
  where
    mx p = do
      (a, b, e') <- opt
      ScpM $ \_ s -> (s { fulfilments = (p, e') : fulfilments s }, ())
      return (a, b, fun p `varApps` abstracted p)


data ScpEnv = ScpEnv {
    statics  :: Statics, -- NB: we do not abstract the h functions over these variables. This helps typechecking and gives GHC a chance to inline the definitions.
    promises :: [Promise]
  }

data ScpState = ScpState {
    names       :: [Var],
    fulfilments :: [(Promise, Out Term)]
  }

newtype ScpM a = ScpM { unScpM :: ScpEnv -> ScpState -> (ScpState, a) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \_ s -> (s, x)
    (!mx) >>= fxmy = ScpM $ \e s -> case unScpM mx e s of (s, x) -> unScpM (fxmy x) e s

instance MonadFix ScpM where
    mfix fmx = ScpM $ \e s -> let (s', x) = unScpM (fmx x) e s in (s', x)

runScpM :: FreeVars -> ScpM (Out Term) -> Out Term
runScpM input_fvs me = uncurry letRec $ snd (unScpM (bindFloats (\_ -> True) me) init_e init_s)
  where
    init_e = ScpEnv { statics = input_fvs, promises = [] }
    init_s = ScpState { names = map (\i -> name $ "h" ++ show (i :: Int)) [0..], fulfilments = [] }


sc, sc' :: History -> (Deeds, State) -> ScpM (Deeds, FreeVars, Out Term)
sc  hist = memo (sc' hist)
sc' hist (deeds, state) = case terminate hist (stateTagBag state) of
    Stop           -> trace "stop" $ split (sc hist)          (deeds, state)
    Continue hist' ->                split (sc hist') (reduce (deeds, state))


memo :: ((Deeds, State) -> ScpM (Deeds, FreeVars, Out Term))
     ->  (Deeds, State) -> ScpM (Deeds, FreeVars, Out Term)
memo opt (deeds, state) = do
    statics <- getStatics
    ps <- getPromises
    case [ (releaseStateDeed deeds state, S.fromList (tb_dynamic_vs ++ tb_static_vs), fun p `varApps` tb_dynamic_vs)
         | p <- ps
         , Just rn_lr <- [match (meaning p) state]
         , let rn_fvs = map (safeRename ("tieback: FVs " ++ pPrintRender (fun p)) rn_lr) -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               tb_dynamic_vs = rn_fvs (abstracted p)
               tb_static_vs  = rn_fvs (lexical p)
          -- Check that all of the things that were dynamic last time are dynamic this time
         , all (\x' -> x' `S.notMember` statics) tb_dynamic_vs
          -- Check that all of the things that were static last time are static this time *and refer to exactly the same thing*
         , and $ zipWith (\x x' -> x' == x && x' `S.member` statics) (lexical p) tb_static_vs -- FIXME: lexical should include transitive lexical vars?
         , traceRender ("memo'", statics, stateFreeVars state, rn_lr, (fun p, lexical p, abstracted p)) True
         ] of
      res:_ -> {- traceRender ("tieback", residualiseState state, fst res) $ -} do
        traceRenderM ("=sc", residualiseState state, deeds, res)
        return res
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        let vs = stateFreeVars state
            (static_vs_list, dynamic_vs_list) = partition (`S.member` statics) (S.toList vs)
    
        -- NB: promises are lexically scoped because they may refer to FVs
        traceRenderM (">sc", residualiseState state, deeds)
        (deeds, _vs', e') <- promise (\x -> P { fun = x, abstracted = dynamic_vs_list, lexical = static_vs_list, meaning = state }) (opt (deeds, state))
        traceRenderM ("<sc", residualiseState state, (deeds, vs, e'))
        
        assertRender ("sc: FVs", _vs' S.\\ vs, vs) (_vs' `S.isSubsetOf` vs) $ return ()
        
        return (deeds, vs, e')

traceRenderM :: (Pretty a, Monad m) => a -> m ()
--traceRenderM x mx = fmap length history >>= \indent -> traceRender (nest indent (pPrint x)) mx
traceRenderM x = traceRender (pPrint x) (return ())
