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

import Termination.Terminate

import Name
import Renaming
import StaticFlags
import Utilities

import Control.Monad.Fix

import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S


supercompile :: Term -> Term
supercompile e = traceRender ("all input FVs", input_fvs) $ runScpM input_fvs $ fmap snd $ sc [] state
  where input_fvs = termFreeVars e
        state = (Heap M.empty reduceIdSupply, [], (mkIdentityRenaming $ S.toList input_fvs, tagTerm tagIdSupply e))


--
-- == Termination ==
--

-- Other functions:
--  Termination.Terminate.terminate

-- This family of functions is the whole reason that I have to thread Tag information throughout the rest of the code:

stateTagBag :: State -> TagBag
stateTagBag (Heap h _, k, (_, e)) = pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` taggedTermTagBag e

pureHeapTagBag :: PureHeap -> TagBag
pureHeapTagBag = plusTagBags . map (taggedTagBag 5 . unTaggedTerm . snd) . M.elems

stackTagBag :: Stack -> TagBag
stackTagBag = plusTagBags . map (taggedTagBag 3)

taggedTermTagBag :: TaggedTerm -> TagBag
taggedTermTagBag = taggedTagBag 2 . unTaggedTerm

taggedTagBag :: Int -> Tagged a -> TagBag
taggedTagBag cls = tagTagBag cls . tag

tagTagBag :: Int -> Tag -> TagBag
tagTagBag cls = mkTagBag . return . injectTag cls


--
-- == Bounded multi-step reduction ==
--

reduce :: State -> State
reduce = go emptyHistory
  where
    go hist state
      | not eVALUATE_PRIMOPS, (_, _, (_, TaggedTerm (Tagged _ (PrimOp _ _)))) <- state = state
      | otherwise = case step state of
        Nothing -> state
        Just state'
          | intermediate state' -> go hist state'
          | otherwise           -> case terminate hist (stateTagBag state') of
              Stop           -> state'
              Continue hist' -> go hist' state'
    
    intermediate :: State -> Bool
    intermediate (_, _, (_, TaggedTerm (Tagged _ (Var _)))) = False
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

bindFloats :: (Promise -> Bool) -> ScpM a -> ScpM ([(Out Var, Out Term)], a)
bindFloats p mx = ScpM $ \e s -> case unScpM mx e s of (s@(ScpState { fulfilments = (partition (p . fst) -> (fs_now, fs_later)) }), x) -> traceRender ("bindFloats", map (fun . fst) fs_now, map (fun . fst) fs_later) $ (s { fulfilments = fs_later }, (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) [(fun p, lambdas (abstracted p) e') | (p, e') <- fs_now], x))

getStatics :: ScpM FreeVars
getStatics = ScpM $ \e s -> (s, statics e)

freshHName :: ScpM Var
freshHName = ScpM $ \_ s -> (s { names = tail (names s) }, expectHead "freshHName" (names s))

getPromises :: ScpM [Promise]
getPromises = ScpM $ \e s -> (s, promises e ++ map fst (fulfilments s))

promise :: (Name -> Promise) -> ScpM (a, Out Term) -> ScpM (a, Out Term)
promise mk_p opt = do
    x <- freshHName
    let p = mk_p x
    ScpM $ \e s -> traceRender ("promise", x) $ unScpM (mx p) e { promises = p : promises e } s
  where
    mx p = do
      (a, e') <- opt
      ScpM $ \_ s -> (s { fulfilments = (p, e') : fulfilments s }, ())
      return (a, fun p `varApps` abstracted p)


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


sc, sc' :: History -> State -> ScpM (FreeVars, Out Term)
sc hist = memo (sc' hist)
sc' hist state = case terminate hist (stateTagBag state) of
    Stop           -> split (sc hist)  state
    Continue hist' -> split (sc hist') (reduce state)


memo :: (State -> ScpM (FreeVars, Out Term))
     -> State -> ScpM (FreeVars, Out Term)
memo opt state = traceRenderM (">tie", residualiseState state) >> do
    statics <- getStatics
    ps <- getPromises
    case [ (S.fromList (tb_dynamic_vs ++ tb_static_vs), fun p `varApps` tb_dynamic_vs)
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
        traceRenderM ("=tie", residualiseState state, res)
        return res
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        let vs = stateFreeVars state
            (static_vs_list, dynamic_vs_list) = partition (`S.member` statics) (S.toList vs)
    
        -- NB: promises are lexically scoped because they may refer to FVs
        (_vs', e') <- promise (\x -> P { fun = x, abstracted = dynamic_vs_list, lexical = static_vs_list, meaning = state }) (opt state)
        -- FIXME: recover the assertion here
        
        traceRenderM ("<tie", residualiseState state, (vs, e'))
        return (vs, e')

traceRenderM :: (Pretty a, Monad m) => a -> m ()
--traceRenderM x mx = fmap length history >>= \indent -> traceRender (nest indent (pPrint x)) mx
traceRenderM x = traceRender (pPrint x) (return ())
