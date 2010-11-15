{-# LANGUAGE TypeOperators #-}
module Evaluator.Syntax where

import Size.Deeds

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Tag

import Renaming
import Utilities

import Algebra.Lattice
import qualified Data.Map as M


type Anned = Tagged :.: FVed
type AnnedTerm = Anned (TermF Anned)
type AnnedValue = ValueF Anned
type AnnedAlt = AltF Anned

annee :: Anned a -> a
annee = fvee . tagee . unComp

annedFreeVars :: Anned a -> FreeVars
annedFreeVars = freeVars . tagee . unComp

annedTag :: Anned a -> Tag
annedTag = tag . unComp


annedVarFreeVars' = taggedFVedVarFreeVars'
annedTermFreeVars = taggedFVedTermFreeVars
annedTermFreeVars' = taggedFVedTermFreeVars'
annedValueFreeVars = taggedFVedValueFreeVars
annedValueFreeVars' = taggedFVedValueFreeVars'
annedAltsFreeVars = taggedFVedAltsFreeVars

renameAnnedVar = renameTaggedFVedVar
renameAnnedTerm = renameTaggedFVedTerm :: IdSupply -> Renaming -> AnnedTerm -> AnnedTerm
renameAnnedValue = renameTaggedFVedValue
renameAnnedValue' = renameTaggedFVedValue'
renameAnnedAlts = renameTaggedFVedAlts

detagAnnedVar = taggedFVedVarToFVedVar
detagAnnedTerm = taggedFVedTermToFVedTerm
detagAnnedValue = taggedFVedValueToFVedValue
detagAnnedValue' = taggedFVedValue'ToFVedValue'
detagAnnedAlts = taggedFVedAltsToFVedAlts


annedVar :: Tag -> Var -> Anned Var
annedVar   tg x = Comp (Tagged tg (FVed (annedVarFreeVars' x)  x))

annedTerm :: Tag -> TermF Anned -> AnnedTerm
annedTerm  tg e = Comp (Tagged tg (FVed (annedTermFreeVars' e)  e))

annedValue :: Tag -> ValueF Anned -> Anned AnnedValue
annedValue tg v = Comp (Tagged tg (FVed (annedValueFreeVars' v) v))


toAnnedTerm :: Term -> AnnedTerm
toAnnedTerm = tagFVedTerm . reflect


type State = (Heap, Stack, In AnnedTerm)

-- | Concrete things bound above are used for values whose allocation might be duplicated.
data BoundWhere = Here (In AnnedTerm)
                | Above (In (Anned AnnedValue))
                deriving (Show)

-- | We do not abstract the h functions over static variables. This helps typechecking and gives GHC a chance to inline the definitions.
data HeapBinding = HB {
    static             :: Bool,
    evaluateMeaning    :: Maybe BoundWhere,
    matchMeaning       :: Maybe (In AnnedTerm),
    terminateMeaning   :: Maybe (Tag, FreeVars),
    residualiseMeaning :: Maybe (In AnnedTerm)
  }
  deriving (Show)

instance BoundedJoinSemiLattice HeapBinding where
    bottom = HB {
        static             = False,
        evaluateMeaning    = Nothing,
        matchMeaning       = Nothing,
        terminateMeaning   = Nothing,
        residualiseMeaning = Nothing
      }

instance JoinSemiLattice HeapBinding where
    hb1 `join` hb2 = HB {
        static             = combine static,
        evaluateMeaning    = combineFirst evaluateMeaning,
        matchMeaning       = combineFirst matchMeaning,
        terminateMeaning   = combineFirst terminateMeaning,
        residualiseMeaning = combineFirst residualiseMeaning
      }
      where combine f = f hb1 `join` f hb2
            combineFirst f = case (f hb1, f hb2) of
                                (Just x,  Nothing) -> Just x
                                (Nothing, Just y)  -> Just y
                                (Just x,  Just _y) -> {-assertRender ("join:HeapBinding", x, _y) (x == _y) $-} Just x
                                _                  -> Nothing

-- FIXME: when supercompiling
--
--   if x then e1[x] else e2[x]
--
-- I want the h-functions for e1 and e2 to be abstracted over x only if x is not a static. If x is a static, I want them to be able
-- to just throw away their Concrete:Here binding for x (from the if) and refer to the lexically bound shared allocation of x.
-- Currently, this is impossible because it requires a binding to be both ((none) or Phantom -- to record the staticness), and
-- Concrete:Here -- to record the value learnt from the case.
--
-- An alternative is to supercompile e1 and e2 with x static and then ensure that we mark x static when it gets introduced. This means
-- the h-functions for e1/e2 will float to the lambda or whatever it is that introduces x, but no further. This is a bit less good, and
-- means that we have to awkwardly plumb around any newly introducedn binders so we can explicitly mark them as "non-static".

type PureHeap = M.Map (Out Var) HeapBinding
data Heap = Heap PureHeap IdSupply
          deriving (Show)

instance NFData BoundWhere where
    rnf (Here a)  = rnf a
    rnf (Above a) = rnf a

instance NFData HeapBinding where
    rnf (HB a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

instance NFData Heap where
    rnf (Heap a b) = rnf a `seq` rnf b

instance Pretty BoundWhere where
    pPrintPrec level prec (Here in_e)  = pPrintPrec level prec in_e
    pPrintPrec level prec (Above in_v) = braces (pPrintPrec level prec in_v)

instance Pretty HeapBinding where
    pPrintPrec _ _ hb = text (show hb)

instance Pretty Heap where
    pPrintPrec level prec (Heap h _) = pPrintPrec level prec h


type Stack = [StackFrame]
data StackFrame = Apply (Out (Anned Var))
                | Scrutinise (In [AnnedAlt])
                | PrimApply PrimOp [In (Anned AnnedValue)] [In AnnedTerm]
                | Update (Out (Anned Var))
                deriving (Show)

instance NFData StackFrame where
    rnf (Apply a)         = rnf a
    rnf (Scrutinise a)    = rnf a
    rnf (PrimApply a b c) = rnf a `seq` rnf b `seq` rnf c
    rnf (Update a)        = rnf a

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn renameAnnedAlts prettyIdSupply in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'

boundWhereTerm :: BoundWhere -> In AnnedTerm
boundWhereTerm (Above (rn, v)) = (rn, fmap Value v)
boundWhereTerm (Here  in_e)    = in_e

{-
concreteHeapBindingTag :: ConcreteHeapBinding -> Tag
concreteHeapBindingTag (Above (_, v)) = annedTag v
concreteHeapBindingTag (Here  (_, e)) = annedTag e

heapBindingNonConcrete :: HeapBinding -> Bool
heapBindingNonConcrete (Concrete _) = False
heapBindingNonConcrete _            = True

heapBindingTerm :: HeapBinding -> Maybe (In AnnedTerm)
heapBindingTerm Environmental  = Nothing
heapBindingTerm (Updated _ _)  = Nothing
heapBindingTerm (Phantom in_e) = Just in_e
heapBindingTerm (Concrete chb) = Just (concreteHeapBindingTerm chb)

heapBindingTag :: HeapBinding -> Maybe Tag
heapBindingTag Environmental    = Nothing
heapBindingTag (Updated tg _)   = Just tg
heapBindingTag (Phantom (_, e)) = Just (annedTag e)
heapBindingTag (Concrete chb)   = Just (concreteHeapBindingTag chb)
-}

stackFrameTags :: StackFrame -> [Tag]
stackFrameTags kf = case kf of
    Apply x'                -> [annedTag x']
    Scrutinise in_alts      -> map (annedTag . snd) (snd in_alts)
    PrimApply _ in_vs in_es -> map (annedTag . snd) in_vs ++ map (annedTag . snd) in_es
    Update x'               -> [annedTag x']

releaseHeapBindingDeeds :: Deeds -> HeapBinding -> Deeds
releaseHeapBindingDeeds deeds hb = maybe deeds (releaseDeedDeep deeds . fst) (terminateMeaning hb)

releaseStateDeed :: Deeds -> State -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> foldl' releaseDeedDeep deeds (stackFrameTags kf))
           (foldl' releaseHeapBindingDeeds
                   (releaseDeedDeep deeds (annedTag e))
                   (M.elems h))
           k
