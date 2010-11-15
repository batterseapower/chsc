{-# LANGUAGE TypeOperators #-}
module Evaluator.Syntax where

import Size.Deeds

import Core.FreeVars
import Core.Renaming
import Core.Syntax
import Core.Tag

import Renaming
import Utilities

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
data ConcreteHeapBinding = Here (In AnnedTerm)
                         | Above (In (Anned AnnedValue))
                         deriving (Show)

-- | We do not abstract the h functions over static variables. This helps typechecking and gives GHC a chance to inline the definitions.
data HeapBinding = Environmental                -- ^ Corresponding variable is static and free in the original input, or the name of a h-function. No need to generalise either of these (remember that h-functions don't appear in the input).
                 | Updated Tag FreeVars         -- ^ Variable is bound by a residualised update frame. TODO: this is smelly and should really be Phantom.
                 | Phantom (In AnnedTerm)       -- ^ Corresponding variable is static static and generated from residualising a term in the splitter. Can use the term information to generalise these.
                 | Concrete ConcreteHeapBinding -- ^ A genuine heap binding that we are actually allowed to look at.
                 deriving (Show)


-- Binding        | Abstract over var? | Use in evaluation? | Examine in matcher? | Generalise?
-- ===============+====================+====================+=====================+============
-- Environmental  | N                  | N                  | N                   | N
-- Updated        | N                  | N                  | N :(                | Y
-- Phantom        | N                  | N                  | Y                   | Y
-- Concrete:Here  | N (Y sometimes..)  | Y (special)        | Y                   | Y
-- Concrete:Above | N                  | Y                  | Y                   | Y
-- (none)         | Y                  | N                  | N                   | N
--
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

instance NFData ConcreteHeapBinding where
    rnf (Here a)  = rnf a
    rnf (Above a) = rnf a

instance NFData HeapBinding where
    rnf Environmental = ()
    rnf (Updated a b) = rnf a `seq` rnf b
    rnf (Phantom a)   = rnf a
    rnf (Concrete a)  = rnf a

instance NFData Heap where
    rnf (Heap a b) = rnf a `seq` rnf b

instance Pretty ConcreteHeapBinding where
    pPrintPrec level prec (Here in_e)  = pPrintPrec level prec in_e
    pPrintPrec level prec (Above in_v) = braces (pPrintPrec level prec in_v)

instance Pretty HeapBinding where
    pPrintPrec _     _    Environmental  = angles empty
    pPrintPrec level _    (Updated x' _) = angles (text "update" <+> pPrintPrec level noPrec x')
    pPrintPrec level _    (Phantom in_e) = angles (pPrintPrec level noPrec in_e)
    pPrintPrec level prec (Concrete chb) = pPrintPrec level prec chb

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


concreteHeapBindingTag :: ConcreteHeapBinding -> Tag
concreteHeapBindingTag (Above (_, v)) = annedTag v
concreteHeapBindingTag (Here  (_, e)) = annedTag e

concreteHeapBindingTerm :: ConcreteHeapBinding -> In AnnedTerm
concreteHeapBindingTerm (Above (rn, v)) = (rn, fmap Value v)
concreteHeapBindingTerm (Here  in_e)    = in_e

heapBindingNonConcrete :: HeapBinding -> Bool
heapBindingNonConcrete (Concrete _) = False
heapBindingNonConcrete _            = True

heapBindingTerm :: HeapBinding -> Maybe (In AnnedTerm)
heapBindingTerm Environmental  = Nothing
heapBindingTerm (Updated _ _)  = Nothing
heapBindingTerm (Phantom in_e) = Just in_e
heapBindingTerm (Concrete chb) = Just (concreteHeapBindingTerm chb)

heapBindingTag :: HeapBinding -> Maybe Tag
heapBindingTag Environmental     = Nothing
heapBindingTag (Updated tg _)    = Just tg
heapBindingTag (Phantom (_, e))  = Just (annedTag e)
heapBindingTag (Concrete chb)    = Just (concreteHeapBindingTag chb)

stackFrameTags :: StackFrame -> [Tag]
stackFrameTags kf = case kf of
    Apply x'                -> [annedTag x']
    Scrutinise in_alts      -> map (annedTag . snd) (snd in_alts)
    PrimApply _ in_vs in_es -> map (annedTag . snd) in_vs ++ map (annedTag . snd) in_es
    Update x'               -> [annedTag x']

releaseHeapBindingDeeds :: Deeds -> HeapBinding -> Deeds
releaseHeapBindingDeeds deeds (Concrete chb) = releaseDeedDeep deeds (concreteHeapBindingTag chb)
releaseHeapBindingDeeds deeds _              = deeds

releaseStateDeed :: Deeds -> State -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> foldl' releaseDeedDeep deeds (stackFrameTags kf))
           (foldl' releaseHeapBindingDeeds
                   (releaseDeedDeep deeds (annedTag e))
                   (M.elems h))
           k
