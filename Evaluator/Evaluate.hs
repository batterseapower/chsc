{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards #-}
module Evaluator.Evaluate (step) where

import Evaluator.FreeVars
import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, (h, k, (rn, TaggedTerm (Tagged tg e)))) = case e of
    Var x             -> force  deeds' h k tg (rename rn x)
    Value v           -> unwind deeds' h k tg (rn, v)
    App e1 x2         -> Just (deeds', (h, Tagged tg (Apply (rename rn x2))            : k, (rn, e1)))
    PrimOp pop (e:es) -> Just (deeds', (h, Tagged tg (PrimApply pop [] (map (rn,) es)) : k, (rn, e)))
    Case e alts       -> Just (deeds', (h, Tagged tg (Scrutinise (rn, alts))           : k, (rn, e)))
    LetRec xes e      -> Just (deeds', allocate h k (rn, (xes, e)))
  where deeds' = releaseDeedDescend_ deeds tg

force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, State)
force deeds (Heap h ids) k tg x' = M.lookup x' h >>= \in_e -> return (deeds, (Heap (M.delete x' h) ids, Tagged tg (Update x') : k, in_e))

unwind :: Deeds -> Heap -> Stack -> Tag -> In TaggedValue -> Maybe (Deeds, State)
unwind deeds h k tg_v in_v = uncons k >>= \(Tagged tg kf, k) -> case kf of
    Apply x2'                 -> return $ apply      (releaseDeedDescend_ deeds tg) h k    tg_v in_v x2'
    Scrutinise in_alts        -> return $ scrutinise (releaseDeedDescend_ deeds tg) h k    tg_v in_v in_alts
    PrimApply pop in_vs in_es -> return $ primop     deeds                          h k tg tg_v pop in_vs in_v in_es
    Update x'                 ->          update     (releaseDeedDescend_ deeds tg) h k    tg_v x' in_v

apply :: Deeds -> Heap -> Stack -> Tag -> In TaggedValue -> Out Var -> (Deeds, State)
apply deeds h k tg_v (rn, Lambda x e_body) x2' = (deeds', (h, k, (insertRenaming x x2' rn, e_body)))
  where deeds' = releaseDeedDescend_ deeds tg_v
apply _     _ _ _    (_,  v)               _   = panic "apply" (pPrint v)

scrutinise :: Deeds -> Heap -> Stack -> Tag -> In TaggedValue -> In [TaggedAlt] -> (Deeds, State)
scrutinise deeds h            k tg_v (_,    Literal l)  (rn_alts, alts)
  | (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
  = (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
scrutinise deeds h            k tg_v (rn_v, Data dc xs) (rn_alts, alts)
  | (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
  = (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
scrutinise deeds (Heap h ids) k tg_v (rn_v, v)          (rn_alts, alts)
  | ((alt_x, alt_e), rest):_ <- [((alt_x, alt_e), rest) | ((DefaultAlt (Just alt_x), alt_e), rest) <- bagContexts alts]
  , (ids', rn_alts', alt_x') <- renameBinder ids rn_alts alt_x
  = (releaseAltDeeds rest deeds, (Heap (M.insert alt_x' (rn_v, TaggedTerm $ Tagged tg_v $ Value v) h) ids', k, (rn_alts', alt_e)))
  | otherwise
  = panic "scrutinise" (pPrint v)

releaseAltDeeds :: [(a, TaggedTerm)] -> Deeds -> Deeds
releaseAltDeeds alts deeds = foldl' (\deeds (_, TaggedTerm in_e) -> releaseDeedDeep deeds (tag in_e)) deeds alts

primop :: Deeds -> Heap -> Stack -> Tag -> Tag -> PrimOp -> [Tagged (In TaggedValue)] -> In TaggedValue -> [In TaggedTerm] -> (Deeds, State)
primop deeds h k tg tg_v2 pop [Tagged tg_v1 (_, Literal (Int l1))] (_, Literal (Int l2)) [] = (releaseDeedDeep (releaseDeedDeep deeds tg) tg_v1, (h, k, (emptyRenaming, TaggedTerm $ Tagged tg_v2 (Value (f pop l1 l2)))))
  where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                            Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                            Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
        retInt  pop l1 l2 = Literal (Int (pop l1 l2))
        retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
primop deeds h k tg tg_v  pop in_vs (rn, v) (in_e:in_es) = (deeds, (h, Tagged tg (PrimApply pop (in_vs ++ [Tagged tg_v (rn, v)]) in_es) : k, in_e))

update :: Deeds -> Heap -> Stack -> Tag -> Out Var -> In TaggedValue -> Maybe (Deeds, State)
update deeds (Heap h ids) k tg_v x' (rn, v)
  | linear    = return (deeds, (Heap h ids, k, (rn, TaggedTerm $ Tagged tg_v (Value v))))
  | otherwise = claimDeed deeds tg_v >>= \deeds -> return (deeds, (Heap (M.insert x' (rn, TaggedTerm $ Tagged tg_v (Value v)) h) ids, k, (rn, TaggedTerm $ Tagged tg_v (Value v))))
  where
    -- If we can GC the update frame (because it can't be referred to in the continuation) then we don't have to actually update the heap or even claim a new deed
    -- TODO: make finding FVs much cheaper (i.e. memoise it in the syntax functor construction)
    -- TODO: could GC cycles as well (i.e. don't consider stuff from the Heap that was only referred to by the thing being removed as "GC roots")
    linear = x' `S.notMember` (pureHeapFreeVars h (stackFreeVars k (inFreeVars taggedValueFreeVars (rn, v))))

allocate :: Heap -> Stack -> In ([(Var, TaggedTerm)], TaggedTerm) -> State
allocate (Heap h ids) k (rn, (xes, e)) = (Heap (h `M.union` M.fromList xes') ids', k, (rn', e))
  where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
