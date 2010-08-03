{-# LANGUAGE ViewPatterns, TupleSections, PatternGuards #-}
module Evaluator.Evaluate (step) where

import Evaluator.Syntax

import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Renaming
import StaticFlags
import Utilities

import qualified Data.Map as M


step :: (State -> State) -> State -> Maybe State
step reduce (h, k, (rn, TaggedTerm (Tagged tg e))) = case e of
    Var x             -> force  h k tg (rename rn x)
    Value v           -> unwind h k    (rn, v)
    App e1 x2         -> Just (h, Tagged tg (Apply (rename rn x2))            : k, (rn, e1))
    PrimOp pop (e:es) -> Just (h, Tagged tg (PrimApply pop [] (map (rn,) es)) : k, (rn, e))
    Case e alts       -> Just (h, Tagged tg (Scrutinise (rn, alts))           : k, (rn, e))
    LetRec xes e      -> Just (allocate h k (rn, (xes, e)))
  where
    force :: Heap -> Stack -> Tag -> Out Var -> Maybe State
    force (Heap h ids) k tg x' = M.lookup x' h >>= \in_e -> return (Heap (M.delete x' h) ids, Tagged tg (Update x') : k, in_e)

    unwind :: Heap -> Stack -> In TaggedValue -> Maybe State
    unwind h k in_v = uncons k >>= \(Tagged tg kf, k) -> return $ case kf of
        Apply x2'                 -> apply      h k    in_v x2'
        Scrutinise in_alts        -> scrutinise h k tg in_v in_alts
        PrimApply pop in_vs in_es -> primop     h k tg pop in_vs in_v in_es
        Update x'                 -> update     h k tg x' in_v

    apply :: Heap -> Stack -> In TaggedValue -> Out Var -> State
    apply h k (rn, Lambda x e_body) x2' = (h, k, (insertRenaming x x2' rn, e_body))
    apply _ _ (_,  v)               _   = panic "apply" (pPrint v)

    scrutinise :: Heap -> Stack -> Tag -> In TaggedValue -> In [TaggedAlt] -> State
    scrutinise h            k _  (_,    Literal l)  (rn_alts, alts)
      | alt_e:_ <- [(rn_alts, alt_e) | (LiteralAlt alt_l, alt_e) <- alts, alt_l == l] ++ [(rn_alts, alt_e) | (DefaultAlt Nothing, alt_e) <- alts] = (h, k, alt_e)
    scrutinise h            k _  (rn_v, Data dc xs) (rn_alts, alts)
      | alt_e:_ <- [(insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e) | (DataAlt alt_dc alt_xs, alt_e) <- alts, alt_dc == dc] ++ [(rn_alts, alt_e) | (DefaultAlt Nothing, alt_e) <- alts] = (h, k, alt_e)
    scrutinise (Heap h ids) k tg (rn_v, v)          (rn_alts, alts)
      | (alt_x, alt_e):_ <- [(alt_x, alt_e) | (DefaultAlt (Just alt_x), alt_e) <- alts]
      , (ids', rn_alts', alt_x') <- renameBinder ids rn_alts alt_x
      = (Heap (M.insert alt_x' (rn_v, TaggedTerm $ Tagged tg $ Value v) h) ids', k, (rn_alts', alt_e))
      | otherwise
      = panic "scrutinise" (pPrint v)

    primop :: Heap -> Stack -> Tag -> PrimOp -> [In TaggedValue] -> In TaggedValue -> [In TaggedTerm] -> State
    primop h k tg pop [(_, Literal (Int l1))] (_, Literal (Int l2)) [] = (h, k, (emptyRenaming, TaggedTerm $ Tagged tg (Value (f pop l1 l2))))
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop h k tg pop in_vs (rn, v) (in_e:in_es) = (h, Tagged tg (PrimApply pop (in_vs ++ [(rn, v)]) in_es) : k, in_e)

    update :: Heap -> Stack -> Tag -> Out Var -> In TaggedValue -> State
    update (Heap h ids) k tg x' (rn, v) = (Heap (M.insert x' (rn, TaggedTerm $ Tagged tg (Value v)) h) ids, k, (rn, TaggedTerm $ Tagged tg (Value v)))

    allocate :: Heap -> Stack -> In ([(Var, TaggedTerm)], TaggedTerm) -> State
    allocate (Heap h ids) k (rn, (xes, e)) = (heap', k, (rn', e))
      where
        (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
        heap' | not sPECULATION = Heap (h `M.union` M.fromList xes') ids'
              | otherwise = foldl' (\(Heap h ids) (x', in_e) -> case reduce (Heap h ids, [], in_e) of
                                                                    (Heap h' ids', [], in_e'@(_, TaggedTerm (Tagged _ (Value _)))) -> Heap (M.insert x' in_e' h') ids' -- Speculation: if we can evaluate to a value "quickly" then use that value,
                                                                    _                                                              -> Heap (M.insert x' in_e  h)  ids) -- otherwise throw away the half-evaluated mess that we reach
                                     (Heap h ids') xes'
