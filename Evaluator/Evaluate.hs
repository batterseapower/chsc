{-# LANGUAGE TupleSections, PatternGuards, ViewPatterns #-}
module Evaluator.Evaluate (Losers, emptyLosers, step) where

import Evaluator.Residualise
import Evaluator.Syntax

import Core.Renaming
import Core.Syntax
import Core.Prelude (trueDataCon, falseDataCon)

import Size.Deeds

import Renaming
import StaticFlags
import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


type Losers = IS.IntSet

emptyLosers :: Losers
emptyLosers = IS.empty


step :: (Deeds, State) -> Maybe (Deeds, State)
step (deeds, _state@(h, k, (rn, e))) =
  (\mb_res -> assertRender (hang (text "step: deeds lost or gained when stepping:") 2 (pPrint (residualiseState _state)))
                           (not dEEDS || maybe True (\(deeds', state') -> noChange (releaseStateDeed deeds _state) (releaseStateDeed deeds' state')) mb_res) mb_res) $
  case annee e of
    Var x             -> force  deeds h k tg (rn, x)
    Value v           -> unwind deeds h k tg (rn, v)
    App e1 x2         -> Just (deeds', (h, Apply (renameAnnedVar rn x2)    : k, (rn, e1)))
    PrimOp _   []     -> error "Nullary primops are called literals :-)"
    PrimOp pop (e:es) -> Just (deeds', (h, PrimApply pop [] (map (rn,) es) : k, (rn, e)))
    Case e alts       -> Just (deeds', (h, Scrutinise (rn, alts)           : k, (rn, e)))
    LetRec xes e      -> Just (allocate deeds' h k (rn, (xes, e)))
  where
    tg = annedTag e
    deeds' = releaseDeedDescend_ deeds tg

    -- When derereferencing an indirection, it is important that the resulting value is not stored anywhere. The reasons are:
    --  1) That would cause allocation to be duplicated if we residualised immediately afterwards, because the value would still be in the heap
    --  2) It would cause a violation of the deeds invariant because *syntax* would be duplicate
    --  3) It feels a bit weird because it might turn phantom stuff into real stuff
    --
    -- Indirections do not change the deeds story much (at all). You have to pay a deed per indirection, which is released
    -- whenever the indirection dies in the process of evaluation (e.g. in the function position of an application). The deeds
    -- that the indirection "points to" are not affected by any of this. The exception is if we *retain* any subcomponent
    -- of the dereferenced thing - in this case we have to be sure to claim some deeds for that subcomponent. For example, if we
    -- dereference to get a lambda in our function application we had better claim deeds for the body.
    dereference :: Heap -> In AnnedValue -> In AnnedValue
    dereference h (rn, Indirect x) | Just (rn', v') <- lookupValue h (safeRename "dereference" rn x) = dereference h (rn', v')
    dereference _ in_v = in_v

    lookupValue :: Heap -> Out Var -> Maybe (In AnnedValue)
    lookupValue (Heap h _) x' = do
        hb <- M.lookup x' h
        -- As a special concession, the evaluator can look into phantom bindings as long as they are already values.
        -- We also take care to residualise any non-linear values as phantoms in the splitter. This stops us from duplicating values.
        (rn, annee -> Value v) <- heapBindingTerm hb
        return (rn, v)

    force :: Deeds -> Heap -> Stack -> Tag -> In Var -> Maybe (Deeds, State)
    force deeds (Heap h ids) k tg (rn, x)
      | Just _ <- lookupValue (Heap h ids) x' = Just (deeds, (Heap h               ids, k,                           (rn, annedTerm tg (Value (Indirect x)))))
      | Just (Concrete in_e) <- M.lookup x' h = Just (deeds, (Heap (M.delete x' h) ids, Update (annedVar tg x') : k, in_e))
      | otherwise                             = Nothing
      where x' = safeRename "force" rn x

    unwind :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Maybe (Deeds, State)
    unwind deeds h k tg_v in_v = uncons k >>= \(kf, k) -> case kf of
        Apply x2'                 -> apply      deeds h k tg_v in_v x2'
        Scrutinise in_alts        -> scrutinise deeds h k tg_v in_v in_alts
        PrimApply pop in_vs in_es -> primop     deeds h k tg_v pop in_vs in_v in_es
        Update x'                 -> update     deeds h k tg_v x' in_v

    apply :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> Out (Anned Var) -> Maybe (Deeds, State)
    apply deeds h k tg_v (dereference h -> (rn, Lambda x e_body)) x2' = fmap (\deeds'' -> (deeds'', (h, k, (insertRenaming x (annee x2') rn, e_body)))) $ claimDeed deeds' (annedTag e_body)
      where
        -- You might wonder why I don't just releaseDeedDescend_ the tg_v here rather than releasing it all and
        -- then claiming a little bit back. The answer is that the tg_v might be the tag of an indirection, so I have
        -- no guarantee that releaseDeedDescend_ will leave me with any deeds for the lambda body!
        deeds' = releaseDeedDeep (releaseDeedDeep deeds (annedTag x2')) tg_v
    apply _     _ _ _    (_,  v)                                  _   = panic "apply" (pPrint v)

    scrutinise :: Deeds -> Heap -> Stack -> Tag -> In AnnedValue -> In [AnnedAlt] -> Maybe (Deeds, State)
    scrutinise deeds (Heap h ids) k tg_v (rn_v, v) (rn_alts, alts)
      | Literal l <- v_deref
      , (alt_e, rest):_ <- [((rn_alts, alt_e), rest) | ((LiteralAlt alt_l, alt_e), rest) <- bagContexts alts, alt_l == l]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h ids, k, alt_e))
      | Data dc xs <- v_deref
      , (alt_e, rest):_ <- [((insertRenamings (alt_xs `zip` map (rename rn_v_deref) xs) rn_alts, alt_e), rest) | ((DataAlt alt_dc alt_xs, alt_e), rest) <- bagContexts alts, alt_dc == dc]
      = Just (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h ids, k, alt_e))
      | ((mb_alt_x, alt_e), rest):_ <- [((mb_alt_x, alt_e), rest) | ((DefaultAlt mb_alt_x, alt_e), rest) <- bagContexts alts]
      = Just $ case mb_alt_x of
                 Nothing    -> (releaseAltDeeds rest (releaseDeedDeep deeds tg_v), (Heap h                                                               ids,  k, (rn_alts,  alt_e)))
                 Just alt_x -> (releaseAltDeeds rest deeds,                        (Heap (M.insert alt_x' (Concrete (rn_v, annedTerm tg_v $ Value v)) h) ids', k, (rn_alts', alt_e)))
                   where (ids', rn_alts', alt_x') = renameBinder ids rn_alts alt_x
                         -- NB: we add the *non-dereferenced* value to the heap in a default branch with variable, because anything else may duplicate allocation
      | otherwise
      = Nothing -- This can legitimately occur, e.g. when supercompiling (if x then (case x of False -> 1) else 2)
      where (rn_v_deref, v_deref) = dereference (Heap h ids) (rn_v, v)

    releaseAltDeeds :: [(a, AnnedTerm)] -> Deeds -> Deeds
    releaseAltDeeds alts deeds = foldl' (\deeds (_, in_e) -> releaseDeedDeep deeds (annedTag in_e)) deeds alts

    primop :: Deeds -> Heap -> Stack -> Tag -> PrimOp -> [In (Anned AnnedValue)] -> In AnnedValue -> [In AnnedTerm] -> Maybe (Deeds, State)
    primop deeds h k tg_v2 pop [(rn_v1, anned_v1)] (rn_v2, v2) []
      | (_, Literal (Int l1)) <- dereference h (rn_v1, annee anned_v1)
      , (_, Literal (Int l2)) <- dereference h (rn_v2, v2)
      = Just (releaseDeedDeep deeds (annedTag anned_v1), (h, k, (emptyRenaming, annedTerm tg_v2 (Value (f pop l1 l2)))))
      | otherwise
      = Nothing -- Can occur legitimately if some of the arguments of the primop are just indirections
      where f pop = case pop of Add -> retInt (+); Subtract -> retInt (-);
                                Multiply -> retInt (*); Divide -> retInt div; Modulo -> retInt mod;
                                Equal -> retBool (==); LessThan -> retBool (<); LessThanEqual -> retBool (<=)
            retInt  pop l1 l2 = Literal (Int (pop l1 l2))
            retBool pop l1 l2 = if pop l1 l2 then Data trueDataCon [] else Data falseDataCon []
    primop deeds h k tg_v  pop in_vs (rn, v) (in_e:in_es) = Just (deeds, (h, PrimApply pop (in_vs ++ [(rn, annedValue tg_v v)]) in_es : k, in_e))
    primop _     _ _ _     _   _     _       _            = Nothing -- Can only occur when the lambda is a dangling indirection

    update :: Deeds -> Heap -> Stack -> Tag -> Anned (Out Var) -> In AnnedValue -> Maybe (Deeds, State)
    update deeds (Heap h ids) k tg_v x' (rn, v) = case claimDeed deeds' tg_v of
        Nothing      -> traceRender ("update: deed claim FAILURE", annee x') Nothing
        Just deeds'' -> Just (deeds'', (Heap (M.insert (annee x') (Concrete (rn, annedTerm tg_v (Value v))) h) ids, k, (mkIdentityRenaming [annee x'], annedTerm tg_v (Value (Indirect (annee x')))))) -- TODO: might be cleaner if I had the update frame renaming?
      where
        -- Unconditionally release the tag associated with the update frame
        deeds' = releaseDeedDeep deeds (annedTag x')

    allocate :: Deeds -> Heap -> Stack -> In ([(Var, AnnedTerm)], AnnedTerm) -> (Deeds, State)
    allocate deeds (Heap h ids) k (rn, (xes, e)) = (deeds, (Heap (h `M.union` M.map Concrete (M.fromList xes')) ids', k, (rn', e)))
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
