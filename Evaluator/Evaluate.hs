{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (Losers, emptyLosers, step) where

import Evaluator.FreeVars
import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import StaticFlags
import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


step :: (FreeVars -> (Losers, Deeds, State) -> (Losers, Deeds, State)) -> FreeVars -> (Losers, Deeds, State) -> Maybe (Losers, Deeds, State)
step reduce live (losers, deeds, _state@(h, k, (rn, e))) =
  (\mb_res -> assertRender (text "step: deeds lost or gained!") (maybe True (\(_, deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) mb_res) $
  case annee e of
    Var x             -> fmap (\(a, b) -> (losers, a, b)) $ force  deeds h k tg (rename rn x)
    Value v           -> fmap (\(a, b) -> (losers, a, b)) $ unwind deeds h k tg (rn, v)
    App e1 x2         -> Just (losers, deeds', (h, Apply (renameAnnedVar rn x2)    : k, (rn, e1)))
    PrimOp pop (e:es) -> Just (losers, deeds', (h, PrimApply pop [] (map (rn,) es) : k, (rn, e)))
    Case e alts       -> Just (losers, deeds', (h, Scrutinise (rn, alts)           : k, (rn, e)))
    LetRec xes e      -> Just (allocate deeds' h k (rn, (xes, e)))
  where
    tg = annedTag e
    deeds' = releaseDeedDescend_ deeds tg

    force :: Deeds -> Heap -> Stack -> Tag -> Out Var -> Maybe (Deeds, State)
    force deeds (Heap h ids) k tg x' = do { Concrete in_e <- M.lookup x' h; return (deeds, (Heap (M.delete x' h) ids, Update (annedVar tg x') : k, in_e)) }

    unwind :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Maybe (Deeds, State)
    unwind deeds h k tg_v in_v = uncons k >>= \(kf, k) -> case kf of
        Apply x2'                 -> return $ apply      deeds h k tg_v in_v x2'
        Scrutinise in_alts        ->          scrutinise deeds h k tg_v in_v in_alts
        PrimApply pop in_vs in_es -> return $ primop     deeds h k tg_v pop in_vs in_v in_es
        Update x'                 ->          update     deeds h k tg_v x' in_v

    apply :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Out (Anned Var) -> (Deeds, State)
    apply deeds h k tg_v (rn, Lambda x e_body) x2' = (deeds', (h, k, (insertRenaming x (annee x2') rn, e_body)))
      where deeds' = releaseDeedDescend_ (releaseDeedDeep deeds (annedTag x2')) tg_v
    apply _     _ _ _    (_,  v)               _   = panic "apply" (pPrint v)

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> In [AnnedAlt] -> Maybe (Deeds, State)
    scrutinise deeds h            k tg_v (_,    Literal l)  (rn_alts, alts)
      | (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds h            k tg_v (rn_v, Data dc xs) (rn_alts, alts)
      | (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc] ++ [((rn_alts, alt_e), rest) | ((DefaultAlt Nothing, alt_e), rest) <- bagContexts alts]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (h, k, alt_e))
    scrutinise deeds (Heap h ids) k tg_v (rn_v, v)          (rn_alts, alts)
      | ((alt_x, alt_e), rest):_ <- [((alt_x, alt_e), rest) | ((DefaultAlt (Just alt_x), alt_e), rest) <- bagContexts alts]
      , (ids', rn_alts', alt_x') <- renameBinder ids rn_alts alt_x
      = Just (releaseAltDeeds rest deeds, (Heap (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value v)) h) ids', k, (rn_alts', alt_e)))
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)

    releaseAltDeeds :: [(a, AnnedTerm)] -> Deeds -> Deeds
    releaseAltDeeds alts deeds = foldl' (\deeds (_, in_e) -> releaseDeedDeep deeds (annedTag in_e)) deeds alts

    primop :: Deeds -> Heap -> Stack -> Tag -> PrimOp -> [In (Anned AnnedValue)] -> In AnnedValue -> [In AnnedTerm] -> (Deeds, State)
    primop deeds h k tg_v2 pop [(_, Comp (Tagged tg_v1 (FVed _ (Literal (Int l1)))))] (_, Literal (Int l2)) [] = (releaseDeedDeep deeds tg_v1, (h, k, (emptyRenaming, annedTerm tg_v2 (Value (f pop l1 l2)))))
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds h k tg_v  pop in_vs (rn, v) (in_e:in_es) = (deeds, (h, PrimApply pop (in_vs ++ [(rn, annedValue tg_v v)]) in_es : k, in_e))

    update :: Deeds -> Heap -> Stack -> Tag -> Anned (Out Var) -> In AnnedValue -> Maybe (Deeds, State)
    update deeds (Heap h ids) k tg_v x' (rn, v)
      | linear    = Just (deeds', (Heap h ids, k, (rn, annedTerm tg_v (Value v))))
      | otherwise = case claimDeed deeds' tg_v of
                      Nothing      -> traceRender ("update: deed claim FAILURE", annee x') Nothing
                      Just deeds'' -> Just (deeds'', (Heap (M.insert (annee x') (Concrete (rn, annedTerm tg_v (Value v))) h) ids, k, (rn, annedTerm tg_v (Value v))))
      where
        -- Unconditionally release the tag associated with the update frame
        deeds' = releaseDeedDeep deeds (annedTag x')

        -- If we can GC the update frame (because it can't be referred to in the continuation) then:
        --  1) We don't have to actually update the heap or even claim a new deed
        --  2) We make the supercompiler less likely to terminate, because doing so tends to reduce TagBag sizes
        --
        -- NB: to prevent incorrectly garbage collecting bindings from the enclosing heap when we have speculation on,
        -- we pass around an extra "live set" of parts of the heap that might be referred to later on
        --
        -- TODO: make finding FVs much cheaper (i.e. memoise it in the syntax functor construction)
        -- TODO: could GC cycles as well (i.e. don't consider stuff from the Heap that was only referred to by the thing being removed as "GC roots")
        linear = sTEP_GARBAGE_COLLECTION &&
                 annee x' `S.notMember` pureHeapFreeVars h (stackFreeVars k (inFreeVars annedValueFreeVars' (rn, v))) &&
                 annee x' `S.notMember` live

    allocate :: Deeds -> Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> (Losers, Deeds, State) -- FIXME: I suspect we should accumulate Losers across the boundary of sc
    allocate deeds (Heap h ids) k (rn, (xes, e)) = (losers', deeds', (heap', k, (rn', e)))
      where
        (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
        (losers', deeds', heap')
          | not sPECULATION = (losers, deeds, Heap (h `M.union` M.map Concrete (M.fromList xes')) ids')
          | otherwise       = (final_losers, final_deeds, Heap (final_h_losers `M.union` final_h_winners) final_ids)
            where
              -- It is *very important* that we prevent speculation from forcing heap-carried things that have proved
              -- to be losers in the past. This prevents us discovering speculation failure of some head binding, and
              -- then forcing several thunks that are each strict in it. This change was motivated by DigitsOfE2 -- it
              -- speeds up supercompilation of that benchmark massively.
              (h_losers, h_winners) = M.partition (\hb -> case hb of Concrete in_e -> annedTag (snd in_e) `IS.member` losers; _ -> False) h
              
              (final_losers, final_deeds, _final_live, final_h_losers, Heap final_h_winners final_ids) = foldl' speculate_one (losers, deeds, S.empty, h_losers, Heap h_winners ids') (xes' `zip` lives')
                
              -- Construct the live set for use when speculating each heap binding. This prevent us from accidentally GCing something that is live
              -- in the "continuation" when speculating a heap binding. We ensure that only those heap bindings that occur *strictly later* than
              -- the binding being speculated contribute to the live set -- this means that GC can still collect stuff that speculation truly makes dead.
              makeLive live in_e = live `S.union` inFreeVars annedTermFreeVars in_e
              (_, lives') = mapAccumR (\live (_x', hb) -> (live `makeLive` hb, live))
                                      (M.fold (\hb live -> live `S.union` heapBindingFreeVars hb) (live `S.union` snd (stackFreeVars k (inFreeVars annedTermFreeVars (rn', e)))) h_losers) xes'
              
              speculate_one (losers, deeds, extra_live, h_losers, Heap h_winners ids) ((x', in_e), live')
                = case reduce (live' `S.union` extra_live) (losers, deeds, (Heap h_winners ids, [], in_e)) of
                    -- NB: commenting in this line is useful if you want to test whether speculation is causing
                    -- a benchmark to be slow due to the cost of the speculation OR due to the extra info. propagation
                    --(rnf -> ()) | False -> undefined
                    _ | not sPECULATE_ON_LOSERS, tg `IS.member` losers                 -> (losers,              deeds,  extra_live `makeLive` in_e, M.insert x' (Concrete in_e) h_losers, Heap h_winners  ids)                         -- Heuristic: don't speculate if it has failed before
                    (losers', deeds', (Heap h' ids', [], in_e'@(_, annee -> Value _))) -> (losers',             deeds', extra_live,                 h_losers,                             Heap (M.insert x' (Concrete in_e') h') ids') -- Speculation: if we can evaluate to a value "quickly" then use that value,
                    _                                                                  -> (IS.insert tg losers, deeds,  extra_live `makeLive` in_e, M.insert x' (Concrete in_e) h_losers, Heap h_winners  ids)                         -- otherwise throw away the half-evaluated mess that we reach
                where tg = annedTag (snd in_e)
