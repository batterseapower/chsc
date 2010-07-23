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
supercompile e = traceRender ("all input FVs", input_fvs) $ runTieM input_fvs $
                 runScpM $ fmap thd3 $ sc [] (deeds, state)
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

data TieEnv = TieEnv {
    statics  :: Statics, -- NB: we do not abstract the h functions over these variables. This helps typechecking and gives GHC a chance to inline the definitions.
    promises :: [Promise]
  }

data TieState = TieState {
    names       :: [Var],
    fulfilments :: [(Promise, Out Term)]
  }

newtype TieM a = TieM { unTieM :: TieEnv -> TieState -> (TieState, a) }

instance Functor TieM where
    fmap = liftM

instance Monad TieM where
    return x = TieM $ \_ s -> (s, x)
    (!mx) >>= fxmy = TieM $ \e s -> case unTieM mx e s of (s, x) -> unTieM (fxmy x) e s

instance MonadStatics TieM where
    withStatics xs mx = bindFloats (\p -> any (`S.member` xs) (lexical p)) $ TieM $ \e s -> unTieM mx (e { statics = statics e `S.union` xs }) s

bindFloats :: (Promise -> Bool) -> TieM a -> TieM ([(Out Var, Out Term)], a)
bindFloats p mx = TieM $ \e s -> case unTieM mx e s of (s@(TieState { fulfilments = (partition (p . fst) -> (fs_now, fs_later)) }), x) -> (s { fulfilments = fs_later }, (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) [(fun p, lambdas (abstracted p) e') | (p, e') <- fs_now], x))

getStatics :: TieM FreeVars
getStatics = TieM $ \e s -> (s, statics e)

freshHName :: TieM Var
freshHName = TieM $ \_ s -> (s { names = tail (names s) }, expectHead "freshHName" (names s))

getPromises :: TieM [Promise]
getPromises = TieM $ \e s -> (s, promises e ++ map fst (fulfilments s))

promise :: (Name -> Promise) -> TieM (Out Term) -> TieM (Out Term)
promise mk_p opt = do
    x <- freshHName
    let p = mk_p x
    TieM $ \e s -> unTieM (mx p) e { promises = p : promises e } s
  where
    mx p = do
      e' <- opt
      TieM $ \_ s -> (s { fulfilments = (p, e') : fulfilments s }, ())
      return (fun p `varApps` abstracted p)

runTieM :: FreeVars -> TieM (Out Term) -> Out Term
runTieM input_fvs mx = uncurry letRec $ snd (unTieM (bindFloats (\_ -> True) mx) init_e init_s)
  where
    init_e = TieEnv { statics = input_fvs, promises = [] }
    init_s = TieState { names = map (\i -> name $ "h" ++ show (i :: Int)) [0..], fulfilments = [] }


data Seen = S {
    seenMeaning :: State,
    seenTie :: TieM (Out Term)
  }

newtype ScpState = ScpState {
    seen :: [Seen]
  }

newtype ScpM a = ScpM { unScpM :: ScpState -> (ScpState, a) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \s -> (s, x)
    (!mx) >>= fxmy = ScpM $ \s -> case unScpM mx s of (s, x) -> unScpM (fxmy x) s

instance MonadFix ScpM where
    mfix fmx = ScpM $ \s -> let (s', x) = unScpM (fmx x) s in (s', x)

getSeen :: ScpM [Seen]
getSeen = ScpM $ \s -> (s, seen s)

saw :: Seen -> ScpM ()
saw n = ScpM $ \s -> (s { seen = n : seen s }, ())

runScpM :: ScpM a -> a
runScpM (ScpM f) = snd (f init_s)
  where init_s = ScpState { seen = [] }


sc, sc' :: History -> (Deeds, State) -> ScpM (Deeds, FreeVars, TieM (Out Term))
sc hist = memo (sc' hist)
sc' hist (deeds, state) = case terminate hist (stateTagBag state) of
    Stop           -> split (sc hist)          (deeds, state)
    Continue hist' -> split (sc hist') (reduce (deeds, state))


memo :: ((Deeds, State) -> ScpM (Deeds, FreeVars, TieM (Out Term)))
     ->  (Deeds, State)  -> ScpM (Deeds, FreeVars, TieM (Out Term))
memo opt (deeds, state) = traceRenderM (">scp", deeds, residualiseState state) >> do
    ns <- getSeen
    case [ (releaseStateDeed deeds state,
            S.fromList $ map (rename rn_lr) $ S.toList n_fvs,
            fmap (\e' -> let xs_hack = S.toList (termFreeVars e' S.\\ n_fvs) -- FIXME: the xs_hack is necessary so we can rename new "h" functions in the output (e.g. h1)
                         in renameTerm (case state of (Heap _ ids, _, _) -> ids) (insertRenamings (xs_hack `zip` xs_hack) rn_lr) e')
                 (seenTie n))
         | n <- ns
         , Just rn_lr <- [match (seenMeaning n) state] -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
         , let n_fvs = stateFreeVars (seenMeaning n)
         ] of
      (deeds, fvs', e'):_ -> do
        traceRenderM ("=scp", residualiseState state, (deeds, fvs'))
        return (deeds, fvs', e')
      [] -> do
        (deeds, fvs', e') <- mfix $ \(~(_deeds, _fvs', tiex)) -> saw S { seenMeaning = state {- NB: Cannot use _fvs' here to improve the FVs at the tieback point because that causes a loop -}, seenTie = tiex } >> fmap (third3 (memo' state)) (opt (deeds, state))
        --assertRender ("sc: FVs", fst res, stateFreeVars state) (fst res `S.isSubsetOf` stateFreeVars state) $ return ()
        traceRenderM ("<scp", residualiseState state, (deeds, fvs'))
        return (deeds, fvs', e')

memo' :: State
      -> TieM (Out Term)
      -> TieM (Out Term)
memo' state opt = traceRenderM (">tie", residualiseState state) >> do
    statics <- getStatics
    ps <- getPromises
    case [ fun p `varApps` tb_dynamic_vs
         | p <- ps
         , Just rn_lr <- [match (meaning p) state]
         , let rn_fvs = map (safeRename ("tieback: FVs " ++ pPrintRender (fun p)) rn_lr) -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               tb_dynamic_vs = rn_fvs (abstracted p)
          -- Check that all of the things that were dynamic last time are dynamic this time
         , all (\x' -> x' `S.notMember` statics) tb_dynamic_vs
          -- Check that all of the things that were static last time are static this time *and refer to exactly the same thing*
         , all (\x -> let x' = rename rn_lr x in x' == x && x' `S.member` statics) (lexical p)
         ] of
      res:_ -> {- traceRender ("tieback", residualiseState state, fst res) $ -} do
        traceRenderM ("=tie", residualiseState state, res)
        return res
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        let (static_vs_list, dynamic_vs_list) = partition (`S.member` statics) (S.toList (stateFreeVars state))
    
        -- NB: promises are lexically scoped because they may refer to FVs
        e' <- promise (\x -> P { fun = x, abstracted = dynamic_vs_list, lexical = static_vs_list, meaning = state }) opt
        
        traceRenderM ("<tie", residualiseState state, e')
        return e'

traceRenderM :: (Pretty a, Monad m) => a -> m ()
--traceRenderM x mx = fmap length history >>= \indent -> traceRender (nest indent (pPrint x)) mx
traceRenderM x = traceRender (pPrint x) (return ())
