{-# LANGUAGE TupleSections #-}
module Supercompile.PostSimplify (inline) where

import Core.FreeVars (altConOpenFreeVars)
import Core.Syntax

import Utilities

import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace


type IsRigidContext = Bool
type Used = M.Map Var IsRigidContext


plusUsed :: Used -> Used -> Used
plusUsed = M.unionWith (\_ _ -> True) -- HACK: ensure that bindings used non-linearly are marked rigid to prevent used-once inlining

plusUseds :: [Used] -> Used
plusUseds = foldr plusUsed M.empty


inline :: Term -> Term
inline = snd . inlineTerm M.empty


inlineTerm :: M.Map Var Term -> Term -> (Used, Term)
inlineTerm h (Term e) = second Term (inlineTerm' h e)

inlineTerm' :: M.Map Var Term -> TermF Term -> (Used, TermF Term)
inlineTerm' h e = case e of
  Var x   -> inlineVar h x
  Value v -> second Value (inlineValue h v)
  App e x -> (used `plusUsed` M.singleton x True, App e' x)
    where (used, e') = inlineTerm h e
  PrimOp pop es -> (plusUseds useds, PrimOp pop es')
    where (useds, es') = unzip $ map (inlineTerm h) es
  Case e alts -> (used `plusUsed` plusUseds alts_useds, Case e' alts')
    where (used, e') = inlineTerm h e
          (alts_useds, alts') = unzip $ map (inlineAlt h) alts
  LetRec xes e -> (foldr M.delete used' (map fst xes), LetRec xes_leave' e')
    where (used, e') = inlineTerm h_loop e
          (xes_used, xes') = unzip [second (x,) (inlineTerm h_loop e) | (x, e) <- xes]
          used' = used `plusUsed` plusUseds xes_used
          
          (xes_inline', xes_leave') = partition (\(x, _) -> M.lookup x used' == Just False && termIsValue (fromJust (lookup x xes))) xes'
          h_loop = h `M.union` M.fromList xes_inline'

inlineVar :: M.Map Var Term -> Var -> (Used, TermF Term)
inlineVar h x = (M.singleton x False, maybe (Var x) (\e -> trace ("inlined " ++ show x) (unTerm e)) (M.lookup x h))

inlineValue :: M.Map Var Term -> Value -> (Used, Value)
inlineValue h v = case v of
  Lambda x e -> (M.delete x used, Lambda x e')
    where (used, e') = inlineTerm h e
  Data dc xs -> (M.fromList (xs `zip` repeat True), Data dc xs)
  Literal l -> (M.empty, Literal l)

inlineAlt :: M.Map Var Term -> Alt -> (Used, Alt)
inlineAlt h (ac, e) = (foldr M.delete used (S.toList bvs), (ac, e'))
  where (used, e') = inlineTerm h e
        (bvs, _) = altConOpenFreeVars ac (S.empty, S.empty)
