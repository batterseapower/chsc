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

import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S


supercompile :: Term -> Term
supercompile e = traceRender ("all input FVs", fvs) $ runScpM fvs $ fmap snd $ sc [] state
  where fvs = termFreeVars e
        state = (Heap M.empty reduceIdSupply, [], (mkIdentityRenaming $ S.toList fvs, tagTerm tagIdSupply e))


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
-- == The drive loop ==
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


data Promise = P {
    fun     :: Var,       -- Name assigned in output program
    fvs     :: [Out Var], -- Abstracted over these variables
    meaning :: State      -- Minimum adequate term
  }

data ScpState = ScpState {
    inputFvs :: FreeVars, -- NB: we do not abstract the h functions over these variables. This helps typechecking and gives GHC a chance to inline the definitions.
    promises :: [Promise],
    outs     :: [(Var, Out Term)],
    names    :: [Var]
  }

get :: ScpM ScpState
get = ScpM $ \s -> (s, s)

put :: ScpState -> ScpM ()
put s = ScpM $ \_ -> (s, ())

modify :: (ScpState -> ScpState) -> ScpM ()
modify f = fmap f get >>= put

freshHName :: ScpM Var
freshHName = ScpM $ \s -> (s { names = tail (names s) }, expectHead "freshHName" (names s))


newtype ScpM a = ScpM { unScpM :: ScpState -> (ScpState, a) }

instance Functor ScpM where
    fmap = liftM

instance Monad ScpM where
    return x = ScpM $ \s -> (s, x)
    (!mx) >>= fxmy = ScpM $ \s -> case unScpM mx s of (s, x) -> unScpM (fxmy x) s

runScpM :: FreeVars -> ScpM (Out Term) -> Out Term
runScpM input_fvs (ScpM f) = letRec (sortBy (comparing ((read :: String -> Int) . drop 1 . name_string . fst)) $ outs s) e'
  where (s, e') = f init_s
        init_s = ScpState { promises = [], names = map (\i -> name $ "h" ++ show (i :: Int)) [0..], outs = [], inputFvs = input_fvs }


sc, sc' :: History -> State -> ScpM (FreeVars, Out Term)
sc hist = memo (sc' hist)
sc' hist state = case terminate hist (stateTagBag state) of
    Stop           -> split (isStop . terminate hist  . stateTagBag) (sc hist)  state
    Continue hist' -> split (isStop . terminate hist' . stateTagBag) (sc hist') (reduce state)


memo :: (State -> ScpM (FreeVars, Out Term))
     -> State -> ScpM (FreeVars, Out Term)
memo opt state = traceRenderM (">sc", residualiseState state) >>
  do
    (ps, input_fvs) <- fmap (promises &&& inputFvs) get
    case [ (S.fromList (rn_fvs (fvs p)), fun p `varApps` rn_fvs tb_noninput_fvs)
         | p <- ps
         , Just rn_lr <- [match (meaning p) state]
         , let rn_fvs = map (safeRename ("tieback: FVs " ++ pPrintRender (fun p)) rn_lr)  -- NB: If tb contains a dead PureHeap binding (hopefully impossible) then it may have a free variable that I can't rename, so "rename" will cause an error. Not observed in practice yet.
               (tb_input_fvs, tb_noninput_fvs) = partition (`S.member` input_fvs) (fvs p)
          -- Because we don't abstract over top-level free variables (this is necessary for type checking e.g. polymorphic uses of error):
         , all (\x -> rename rn_lr x == x) tb_input_fvs
         ] of
      res:_ -> {- traceRender ("tieback", residualiseState state, fst res) $ -} do
        traceRenderM ("<sc", residualiseState state, res)
        return res
      [] -> {- traceRender ("new drive", residualiseState state) $ -} do
        x <- freshHName
        let vs = stateFreeVars state
            vs_list = S.toList vs
            noninput_vs_list = filter (`S.notMember` input_fvs) vs_list
        traceRenderM ("memo", x, vs_list) `seq` return ()
        
        promise P { fun = x, fvs = vs_list, meaning = state }
        (_fvs', e') <- opt state
        assertRender ("sc: FVs", _fvs', vs) (_fvs' `S.isSubsetOf` vs) $ return ()
        
        traceRenderM ("<sc", residualiseState state, (S.fromList vs_list, e'))
        
        bind x (lambdas noninput_vs_list e')
        return (vs, x `varApps` noninput_vs_list)


promise :: Promise -> ScpM ()
promise p = modify (\s -> s { promises = p : promises s })

bind :: Var -> Out Term -> ScpM ()
bind x e = modify (\s -> s { outs = (x, e) : outs s })

traceRenderM :: Pretty a => a -> ScpM ()
--traceRenderM x mx = fmap length history >>= \indent -> traceRender (nest indent (pPrint x)) mx
traceRenderM x = traceRender (pPrint x) (return ())
