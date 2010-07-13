{-# LANGUAGE TupleSections, PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Supercompile.Match (match) where

import Core.Renaming
import Core.Syntax

import Evaluator.Syntax

import Renaming
import Utilities

import qualified Data.Map as M


match :: State -- ^ Tieback semantics
      -> State -- ^ This semantics
      -> Maybe Renaming -- ^ Renaming from left to right
match (Heap h_l _, k_l, in_e_l) (Heap h_r _, k_r, in_e_r) = -- (\res -> traceRender ("match", M.keysSet h_l, residualiseDriveState (Heap h_l prettyIdSupply, k_l, in_e_l), M.keysSet h_r, residualiseDriveState (Heap h_r prettyIdSupply, k_r, in_e_r), res) res) $
  do
    free_eqs1 <- matchInTerm matchIdSupply in_e_l in_e_r
    (bound_eqs, free_eqs2) <- matchEC k_l k_r
    matchHeapExact h_l h_r (bound_eqs, free_eqs1 ++ free_eqs2)

matchInTerm :: IdSupply -> In TaggedTerm -> In TaggedTerm -> Maybe [(Var, Var)]
matchInTerm ids (rn_l, TaggedTerm (Tagged _ e_l)) (rn_r, TaggedTerm (Tagged _ e_r)) = matchInTerm' ids (rn_l, e_l) (rn_r, e_r)

matchInTerm' :: IdSupply -> In (TermF TaggedTerm) -> In (TermF TaggedTerm) -> Maybe [(Var, Var)]
matchInTerm' _   (rn_l, Var x_l)           (rn_r, Var x_r)           = Just [matchInVar (rn_l, x_l) (rn_r, x_r)]
matchInTerm' ids (rn_l, Value v_l)         (rn_r, Value v_r)         = matchInValue ids (rn_l, v_l) (rn_r, v_r)
matchInTerm' ids (rn_l, App e_l x_l)       (rn_r, App e_r x_r)       = matchInTerm ids (rn_l, e_l) (rn_r, e_r) >>= \eqs -> return (matchInVar (rn_l, x_l) (rn_r, x_r) : eqs)
matchInTerm' ids (rn_l, PrimOp pop_l es_l) (rn_r, PrimOp pop_r es_r) = guard (pop_l == pop_r) >> matchInList (matchInTerm ids) (rn_l, es_l) (rn_r, es_r)
matchInTerm' ids (rn_l, Case e_l alts_l)   (rn_r, Case e_r alts_r)   = liftM2 (++) (matchInTerm ids (rn_l, e_l) (rn_r, e_r)) (matchInAlts ids (rn_l, alts_l) (rn_r, alts_r))
matchInTerm' ids (rn_l, LetRec xes_l e_l)  (rn_r, LetRec xes_r e_r)  = matchInTerm ids'' (rn_l', e_l) (rn_r', e_r) >>= \eqs -> matchPureHeapExact ids'' [] eqs (M.fromList xes_l') (M.fromList xes_r')
  where (ids',  rn_l', xes_l') = renameBounds (\_ x' -> x') ids  rn_l xes_l
        (ids'', rn_r', xes_r') = renameBounds (\_ x' -> x') ids' rn_r xes_r
matchInTerm' _ _ _ = Nothing

matchInValue :: IdSupply -> In TaggedValue -> In TaggedValue -> Maybe [(Var, Var)]
matchInValue ids (rn_l, Lambda x_l e_l) (rn_r, Lambda x_r e_r) = matchInTerm ids'' (rn_l', e_l) (rn_r', e_r) >>= \eqs -> matchRigidBinders [(x_l', x_r')] eqs
  where (ids',  rn_l', x_l') = renameBinder ids  rn_l x_l
        (ids'', rn_r', x_r') = renameBinder ids' rn_r x_r
matchInValue _   (rn_l, Data dc_l xs_l) (rn_r, Data dc_r xs_r) = guard (dc_l == dc_r) >> matchInVars (rn_l, xs_l) (rn_r, xs_r)
matchInValue _   (_,    Literal l_l)    (_,    Literal l_r)    = guard (l_l == l_r) >> return []
matchInValue _ _ _ = Nothing

matchInAlts :: IdSupply -> In [TaggedAlt] -> In [TaggedAlt] -> Maybe [(Var, Var)]
matchInAlts ids (rn_l, alts_l) (rn_r, alts_r) = zipWithEqual (matchInAlt ids) (map (rn_l,) alts_l) (map (rn_r,) alts_r) >>= (fmap concat . sequence)

matchInAlt :: IdSupply -> In TaggedAlt -> In TaggedAlt -> Maybe [(Var, Var)]
matchInAlt ids (rn_l, (alt_con_l, alt_e_l)) (rn_r, (alt_con_r, alt_e_r)) = matchAltCon alt_con_l' alt_con_r' >>= \binders -> matchInTerm ids'' (rn_l', alt_e_l) (rn_r', alt_e_r) >>= \eqs -> matchRigidBinders binders eqs
  where (ids',  rn_l', alt_con_l') = renameAltCon ids  rn_l alt_con_l
        (ids'', rn_r', alt_con_r') = renameAltCon ids' rn_r alt_con_r

matchAltCon :: AltCon -> AltCon -> Maybe [(Var, Var)]
matchAltCon (DataAlt dc_l xs_l) (DataAlt dc_r xs_r) = guard (dc_l == dc_r) >> return (xs_l `zip` xs_r)
matchAltCon (LiteralAlt l_l)    (LiteralAlt l_r)    = guard (l_l == l_r) >> return []
matchAltCon (DefaultAlt mb_x_l) (DefaultAlt mb_x_r) = matchMaybe matchVar mb_x_l mb_x_r
matchAltCon _ _ = Nothing

matchVar :: Out Var -> Out Var -> (Var, Var)
matchVar x_l' x_r' = (x_l', x_r')

matchInVar :: In Var -> In Var -> (Var, Var)
matchInVar (rn_l, x_l) (rn_r, x_r) = (safeRename "matchInVar: Left" rn_l x_l, safeRename "matchInVar: Right" rn_r x_r)

matchInVars :: In [Var] -> In [Var] -> Maybe [(Var, Var)]
matchInVars = matchInList (\x_l' x_r' -> return [matchInVar x_l' x_r'])

matchInList :: (In a -> In a -> Maybe [(Var, Var)])
            -> In [a] -> In [a] -> Maybe [(Var, Var)]
matchInList match (rn_l, xs_l) (rn_r, xs_r) = fmap concat $ zipWithEqualM match (map (rn_l,) xs_l) (map (rn_r,) xs_r)

matchList :: (a -> a -> Maybe [(Var, Var)])
          -> [a] -> [a] -> Maybe [(Var, Var)]
matchList match xs_l xs_r = fmap concat (zipWithEqualM match xs_l xs_r)

matchMaybe :: (a -> a -> (Var, Var))
           -> Maybe a -> Maybe a -> Maybe [(Var, Var)]
matchMaybe _ Nothing    Nothing    = Just []
matchMaybe f (Just x_l) (Just x_r) = Just [f x_l x_r]
matchMaybe _ _ _ = Nothing

matchEC :: Stack -> Stack -> Maybe ([(Var, Var)], [(Var, Var)])
matchEC k_l k_r = fmap combine $ zipWithEqualM (\kf_l kf_r -> matchECFrame (tagee kf_l) (tagee kf_r)) k_l k_r
  where combine = (concat *** concat) . unzip

matchECFrame :: StackFrame -> StackFrame -> Maybe ([(Var, Var)], [(Var, Var)])
matchECFrame (Apply x_l')                      (Apply x_r')                      = Just ([], [matchVar x_l' x_r'])
matchECFrame (Scrutinise in_alts_l)            (Scrutinise in_alts_r)            = fmap ([],) $ matchInAlts matchIdSupply in_alts_l in_alts_r
matchECFrame (PrimApply pop_l in_vs_l in_es_l) (PrimApply pop_r in_vs_r in_es_r) = fmap ([],) $ guard (pop_l == pop_r) >> liftM2 (++) (matchList (\v1 v2 -> matchInValue matchIdSupply (tagee v1) (tagee v2)) in_vs_l in_vs_r) (matchList (matchInTerm matchIdSupply) in_es_l in_es_r)
matchECFrame (Update x_l')                     (Update x_r')                     = Just ([matchVar x_l' x_r'], [])
matchECFrame _ _ = Nothing

-- Returns a renaming from the list only if the list maps a "left" variable to a unique "right" variable
safeMkRenaming :: [(Var, Var)] -> Maybe Renaming
safeMkRenaming eqs = guard (all (\(x_l, x_r) -> safeRename "safeMkRenaming" rn x_l == x_r) eqs) >> return rn
  where rn = mkRenaming eqs

matchRigidBinders :: [(Var, Var)] -> [(Var, Var)] -> Maybe [(Var, Var)]
matchRigidBinders bound_eqs eqs = do
    occursCheck bound_eqs eqs
    return $ filter (`notElem` bound_eqs) eqs

-- The occurs check is trigged by one of these two situations:
--   x |-> Just y_l;  (update y_l)<x> `match` x |-> Just free; (update y_r)<x>   Can't instantiate y_l with free since its not a template var
--   x |-> Just tmpl; (update y_l)<x> `match` x |-> Just y_r;  (update y_r)<x>   Can't instantiate tmpl with y_r since y_r is bound locally
occursCheck :: [(Var, Var)] -> [(Var, Var)] -> Maybe ()
occursCheck bound_eqs eqs = guard $ not $ any (\(x_l, x_r) -> any (\(bound_x_l, bound_x_r) -> (x_l == bound_x_l) /= (x_r == bound_x_r)) bound_eqs) eqs

-- NB: if there are dead bindings in the left PureHeap then the output Renaming will not contain a renaming for their binders.
matchHeapExact :: PureHeap -> PureHeap -> ([(Var, Var)], [(Var, Var)]) -> Maybe Renaming
matchHeapExact init_h_l init_h_r (bound_eqs, free_eqs) = do
    -- 1) Find the initial matching by simply recursively matching used bindings from the Left
    --    heap against those from the Right heap (if any)
    eqs <- matchPureHeapExact matchIdSupply bound_eqs free_eqs init_h_l init_h_r
    -- 2) Perhaps we violate the occurs check?
    occursCheck bound_eqs eqs
    -- 3) If the left side var was free, we might have assumed two different corresponding rights for it. This is not necessarily a problem:
    --      ()<(a, a)> `match` c |-> True; d |-> True; ()<(c, d)>
    --      ()<(a, a)> `match` c |-> True; d |-> c; ()<(c, d)>
    --    But for now I'm going to mandate that the mapping must be trivially injective.
    safeMkRenaming eqs

matchPureHeapExact :: IdSupply -> [(Var, Var)] -> [(Var, Var)] -> PureHeap -> PureHeap -> Maybe [(Var, Var)]
matchPureHeapExact ids bound_eqs free_eqs init_h_l init_h_r = do
    -- 1) Find the initial matching by simply recursively matching used bindings from the Left
    --    heap against those from the Right heap (if any)
    eqs <- matchPureHeap ids bound_eqs free_eqs init_h_l init_h_r
    -- 2) The outgoing equalities should only relate x_l's that are not bound by init_h_l
    --    because we don't the local bound variables I've generated from matchingIdSupply "leaking" upwards
    eqs <- return $ filter (\(x_l, _x_r) -> x_l `M.notMember` init_h_l) eqs
    -- 3) Now the problem is that there might be some bindings in the Right heap that are referred
    --    to by eqs. We want an exact match, so we can't allow that.
    guard $ all (\(_x_l, x_r) -> x_r `M.notMember` init_h_r) eqs
    -- 4) We now know that all of the variables bound by both init_h_l and init_h_r are not mentioned
    --    in the outgoing equalities, which is what we want for an exact match.
    --     NB: We use this function when matching letrecs, so don't necessarily want to build a renaming immediately
    return eqs

matchPureHeap :: IdSupply -> [(Var, Var)] -> [(Var, Var)] -> PureHeap -> PureHeap -> Maybe [(Var, Var)]
matchPureHeap ids bound_eqs free_eqs init_h_l init_h_r = go bound_eqs free_eqs init_h_l init_h_r
  where
    -- Utility function used to deal with work-duplication issues when matching
    deleteExpensive x m | Just (_, e) <- M.lookup x m, not (taggedTermIsCheap e) = M.delete x m
                        | otherwise = m
    
    -- NB: must respect work-sharing for non-values
    --  x |-> e1, y |-> e1; (x, y) `match` x |-> e1; (x, x) == Nothing
    --  x |-> e1; (x, x) `match` x |-> e1; y |-> e1; (x, y) == Nothing (though this is more questionable, it seems a consistent choice)
    -- NB: treat equal values as equal regardless of duplication
    --  x |-> v, y |-> v; (x, y) `match` x |-> v; (x, x) /= Nothing
    -- TODO: look through variables on both sides
    --  x |-> e1; (x, x) `match` x |-> e1; y |-> x `match` (x, y) /= Nothing
    --  x |-> e1, y |-> x; (x, y) `match` x |-> e1 `match` (x, x) /= Nothing
    go known [] _ _ = Just known
    go known ((x_l, x_r):free_eqs) h_l h_r
       -- Perhaps we have already assumed this equality is true?
      | (x_l, x_r) `elem` known = go known free_eqs h_l h_r
       -- Perhaps the left side is bound, so we need to match it against a corresponding right?
      | Just in_e_l <- M.lookup x_l h_l = M.lookup x_r h_r >>= \in_e_r -> matchInTerm ids in_e_l in_e_r >>= \extra_free_eqs -> go ((x_l, x_r) : known) (extra_free_eqs ++ free_eqs) (deleteExpensive x_l h_l) (deleteExpensive x_r h_r)
       -- Perhaps the left side was originally bound, but we already matched it against something else?
      | M.member x_l init_h_l = Nothing
       -- The left side is free, so assume that we can instantiate x_l to x_r (x_l may be bound above, x_r may be bound here or above):
      | otherwise = go ((x_l, x_r) : known) free_eqs h_l h_r
