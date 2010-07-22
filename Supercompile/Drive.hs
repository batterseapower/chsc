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

import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S
import Data.Tree


supercompile :: Term -> Term
supercompile e = traceRender ("all input FVs", fvs) $
                 runScpM fvs $ fmap thd3 $ sc [] (deeds, state)
  where fvs = termFreeVars e
        state = (Heap M.empty reduceIdSupply, [], (mkIdentityRenaming $ S.toList fvs, tagged_e))
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
-- == The drive loop ==
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


data Promise = P {
    fun     :: Var,       -- Name assigned in output program
    fvs     :: [Out Var], -- Abstracted over these variables
    meaning :: State      -- Minimum adequate term
  }

data ScpState = ScpState {
    scp_input_fvs :: FreeVars, -- NB: we do not abstract the h functions over these variables. This helps typechecking and gives GHC a chance to inline the definitions.
    scp_promises  :: [Promise],
    scp_outs      :: [(Var, Out Term)],
    scp_names     :: [Var]
  }

get :: ScpM ScpState
get = ScpM $ \s -> (s, s)

put :: ScpState -> ScpM ()
put s = ScpM $ \_ -> (s, ())

modify :: (ScpState -> ScpState) -> ScpM ()
modify f = fmap f get >>= put

freshHName :: ScpM Var
freshHName = ScpM $ \s -> (s { scp_names = tail (scp_names s) }, expectHead "freshHName" (scp_names s))


newtype ScpM a = ScpM { unScpM :: ScpState -> (ScpState, a) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \s -> (s, x)
    (!mx) >>= fxmy = ScpM $ \s -> case unScpM mx s of (s, x) -> unScpM (fxmy x) s

runScpM :: FreeVars -> ScpM (Out Term) -> Out Term
runScpM input_fvs (ScpM f) = letRec (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) $ scp_outs s) e'
  where (s, e') = f init_s
        init_s = ScpState { scp_promises = [], scp_names = map (\i -> name $ "h" ++ show (i :: Int)) [0..], scp_outs = [], scp_input_fvs = input_fvs }


sc, sc' :: History -> (Deeds, State) -> ScpM (Deeds, FreeVars, Out Term)
sc  hist = memo (sc' hist)
sc' hist (deeds, state) = case terminate hist (stateTagBag state) of
    Stop           -> trace "stop" $ split (sc hist)          (deeds, state)
    Continue hist' ->                split (sc hist') (reduce (deeds, state))


memo :: ((Deeds, State) -> ScpM (Deeds, FreeVars, Out Term))
     ->  (Deeds, State) -> ScpM (Deeds, FreeVars, Out Term)
memo opt (deeds, state) = do
    (ps, input_fvs) <- fmap (scp_promises &&& scp_input_fvs) get
    case [ (fun p, S.fromList (rn_fvs (fvs p)), fun p `varApps` rn_fvs tb_noninput_fvs)
         | p <- ps
         , Just rn_lr <- [match (meaning p) state]
         , let rn_fvs = map (safeRename ("tieback: FVs " ++ pPrintRender (fun p)) rn_lr)  -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               (tb_input_fvs, tb_noninput_fvs) = partition (`S.member` input_fvs) (fvs p)
          -- Because we don't abstract over top-level free variables (this is necessary for type checking e.g. polymorphic uses of error):
         , all (\x -> rename rn_lr x == x) tb_input_fvs
         ] of
      (_x, fvs', e'):_ -> {- traceRender ("tieback", residualiseState state, fst res) $ -} do
        traceRenderM ("=sc", _x, residualiseState state, (fvs', e'))
        return (releaseStateDeed deeds state, fvs', e')
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        x <- freshHName
        let vs = stateFreeVars state
            vs_list = S.toList vs
            noninput_vs_list = filter (`S.notMember` input_fvs) vs_list
        traceRenderM ("memo", x, vs_list) `seq` return ()
        
        promise P { fun = x, fvs = vs_list, meaning = state }
        
        traceRenderM (">sc", x, deeds, residualiseState state)
        (deeds, _fvs', e') <- opt (deeds, state)
        traceRenderM ("<sc", x, deeds, residualiseState state, (S.fromList vs_list, e'))
        
        assertRender ("sc: FVs", x, _fvs' S.\\ vs, vs) (_fvs' `S.isSubsetOf` vs) $ return ()
        
        bind x (lambdas noninput_vs_list e')
        return (deeds, vs, x `varApps` noninput_vs_list)


promise :: Promise -> ScpM ()
promise p = modify (\s -> s { scp_promises = p : scp_promises s })

bind :: Var -> Out Term -> ScpM ()
bind x e = modify (\s -> s { scp_outs = (x, e) : scp_outs s })

traceRenderM :: Pretty a => a -> ScpM ()
--traceRenderM x = fmap ((length . promises) &&& (length . outs)) get >>= \(a, b) -> traceRender (nest (a - b) (pPrint x)) (return ())
traceRenderM x = traceRender (pPrint x) (return ())
