{-# LANGUAGE TypeOperators #-}
module Evaluator.Syntax where

import Size.Deeds

import Core.FreeVars
import Core.Renaming
import Core.Size
import Core.Syntax
import Core.Tag

import Renaming
import StaticFlags
import Utilities

import Algebra.Lattice

import qualified Data.Map as M


type Anned = Tagged :.: Sized :.: FVed
type AnnedTerm = Anned (TermF Anned)
type AnnedValue = ValueF Anned
type AnnedAlt = AltF Anned

annee :: Anned a -> a
annee = extract

annedSize :: Anned a -> Size
annedSize = size . unComp . tagee . unComp

annedFreeVars :: Anned a -> FreeVars
annedFreeVars = freeVars . sizee . unComp . tagee . unComp

annedTag :: Anned a -> Tag
annedTag = tag . unComp


annedVarFreeVars' = taggedSizedFVedVarFreeVars'
annedTermFreeVars = taggedSizedFVedTermFreeVars
annedTermFreeVars' = taggedSizedFVedTermFreeVars'
annedValueFreeVars = taggedSizedFVedValueFreeVars
annedValueFreeVars' = taggedSizedFVedValueFreeVars'
annedAltsFreeVars = taggedSizedFVedAltsFreeVars

annedVarSize' = taggedSizedFVedVarSize'
annedTermSize' = taggedSizedFVedTermSize'
annedTermSize = taggedSizedFVedTermSize
annedValueSize' = taggedSizedFVedValueSize'
annedValueSize = taggedSizedFVedValueSize
annedAltsSize = taggedSizedFVedAltsSize

renameAnnedTerm = renameTaggedSizedFVedTerm :: IdSupply -> Renaming -> AnnedTerm -> AnnedTerm
renameAnnedValue = renameTaggedSizedFVedValue
renameAnnedValue' = renameTaggedSizedFVedValue'
renameAnnedAlts = renameTaggedSizedFVedAlts

detagAnnedTerm = taggedSizedFVedTermToFVedTerm
detagAnnedValue = taggedSizedFVedValueToFVedValue
detagAnnedValue' = taggedSizedFVedValue'ToFVedValue'
detagAnnedAlts = taggedSizedFVedAltsToFVedAlts


annedVar :: Tag -> Var -> Anned Var
annedVar   tg x = Comp (Tagged tg (Comp (Sized (annedVarSize' x)   (FVed (annedVarFreeVars' x)  x))))

annedTerm :: Tag -> TermF Anned -> AnnedTerm
annedTerm  tg e = Comp (Tagged tg (Comp (Sized (annedTermSize' e)  (FVed (annedTermFreeVars' e)  e))))

annedValue :: Tag -> ValueF Anned -> Anned AnnedValue
annedValue tg v = Comp (Tagged tg (Comp (Sized (annedValueSize' v) (FVed (annedValueFreeVars' v) v))))


toAnnedTerm :: Term -> AnnedTerm
toAnnedTerm = tagFVedTerm . reflect


data WhyLive = PhantomLive | ConcreteLive
             deriving (Eq, Show)

instance Pretty WhyLive where
    pPrint = text . show

instance NFData WhyLive

instance JoinSemiLattice WhyLive where
    ConcreteLive `join` _            = ConcreteLive
    _            `join` ConcreteLive = ConcreteLive
    _            `join` _            = PhantomLive

instance BoundedJoinSemiLattice WhyLive where
    bottom = PhantomLive


data QA = Question Var
        | Answer   (ValueF Anned)

instance Pretty QA where
    pPrintPrec level prec = pPrintPrec level prec . qaToAnnedTerm'

qaToAnnedTerm' :: QA -> TermF Anned
qaToAnnedTerm' (Question x) = Var x
qaToAnnedTerm' (Answer v)   = Value v


type UnnormalisedState = (Heap, Stack, In AnnedTerm)
type State = (Heap, Stack, In (Anned QA))

denormalise :: State -> UnnormalisedState
denormalise (h, k, (rn, qa)) = (h, k, (rn, fmap qaToAnnedTerm' qa))

-- | We do not abstract the h functions over static variables. This helps typechecking and gives GHC a chance to inline the definitions.
data HeapBinding = Environmental                     -- ^ Corresponding variable is static and free in the original input, or the name of a h-function. No need to generalise either of these (remember that h-functions don't appear in the input).
                 | Updated Tag FreeVars              -- ^ Variable is bound by a residualised update frame. TODO: this is smelly and should really be Phantom.
                 | Phantom (In AnnedTerm)            -- ^ Corresponding variable is static static and generated from residualising a term in the splitter. Can use the term information to generalise these.
                 | Concrete (In AnnedTerm)           -- ^ A genuine heap binding that we are actually allowed to look at.
                 | Unfolding (In (Anned AnnedValue)) -- ^ Unfolding for some variable: both heap binding and internal variables will be lambda-abstracted over
                 deriving (Show)

type PureHeap = M.Map (Out Var) HeapBinding
data Heap = Heap PureHeap IdSupply
          deriving (Show)

instance NFData HeapBinding where
    rnf Environmental = ()
    rnf (Updated a b) = rnf a `seq` rnf b
    rnf (Phantom a)   = rnf a
    rnf (Concrete a)  = rnf a
    rnf (Unfolding a) = rnf a

instance NFData Heap where
    rnf (Heap a b) = rnf a `seq` rnf b

instance Pretty HeapBinding where
    pPrintPrec _     _    Environmental    = angles empty
    pPrintPrec level _    (Updated x' _)   = angles (text "update" <+> pPrintPrec level noPrec x')
    pPrintPrec level _    (Phantom in_e)   = angles (pPrintPrec level noPrec in_e)
    pPrintPrec level prec (Concrete in_e)  = pPrintPrec level prec in_e
    pPrintPrec level _    (Unfolding in_v) = bananas (pPrintPrec level noPrec in_v)

instance Pretty Heap where
    pPrintPrec level prec (Heap h _) = pPrintPrec level prec h


type Stack = [Tagged StackFrame]
data StackFrame = Apply (Out Var)
                | Scrutinise (In [AnnedAlt])
                | PrimApply PrimOp [In (Anned AnnedValue)] [In AnnedTerm]
                | Update (Out Var)
                deriving (Show)

instance NFData StackFrame where
    rnf (Apply a)         = rnf a
    rnf (Scrutinise a)    = rnf a
    rnf (PrimApply a b c) = rnf a `seq` rnf b `seq` rnf c
    rnf (Update a)        = rnf a

instance Pretty StackFrame where
    pPrintPrec level prec kf = case kf of
        Apply x'                  -> pPrintPrecApp level prec (text "[_]") x'
        Scrutinise in_alts        -> pPrintPrecCase level prec (text "[_]") (renameIn (renameAnnedAlts prettyIdSupply) in_alts)
        PrimApply pop in_vs in_es -> pPrintPrecPrimOp level prec pop (map SomePretty in_vs ++ map SomePretty in_es)
        Update x'                 -> pPrintPrecApp level prec (text "update") x'


heapBindingPhantom :: HeapBinding -> Bool
heapBindingPhantom (Concrete _)  = False
heapBindingPhantom (Unfolding _) = False
heapBindingPhantom _             = True

heapBindingEnvironmental :: HeapBinding -> Bool
heapBindingEnvironmental Environmental = True
heapBindingEnvironmental _             = False

-- A heap binding is a value if the binding above is likely to be discovered to be a value by GHC. Used for heuristics about local heap bindings.
heapBindingProbablyValue :: HeapBinding -> Bool
heapBindingProbablyValue Environmental   = True                                         -- Top level bindings are often functions and hence values
heapBindingProbablyValue (Updated _ _)   = False                                        -- Almost certainly not values since the supercompiler stopped in the process of evaluating them
heapBindingProbablyValue (Phantom in_e)  = sPECULATION `implies` termIsValue (snd in_e) -- I used to do `termIsValue (snd in_e)` here. However, that means that (if we aren't speculating) we kill phantomness for things that are phantom and close to being values if we run out of deeds for them, which is sad
heapBindingProbablyValue (Unfolding _)   = True                                         -- Well, duh
heapBindingProbablyValue (Concrete _)    = True                                         -- We can't really say yet since we may not have supercompiled the RHS

heapBindingTerm :: HeapBinding -> Maybe (In AnnedTerm, WhyLive)
heapBindingTerm Environmental    = Nothing
heapBindingTerm (Updated _ _)    = Nothing
heapBindingTerm (Phantom in_e)   = Just (in_e, PhantomLive)
heapBindingTerm (Unfolding in_v) = Just (second (fmap Value) in_v, ConcreteLive)
heapBindingTerm (Concrete in_e)  = Just (in_e, ConcreteLive)

heapBindingTag_ :: HeapBinding -> Maybe Tag
heapBindingTag_ = fmap fst . heapBindingTag

heapBindingTag :: HeapBinding -> Maybe (Tag, Bool) -- The boolean tells us whether we have claimed deeds for the binding's tag
heapBindingTag Environmental      = Nothing
heapBindingTag (Updated tg _)     = Just (tg,         False)
heapBindingTag (Phantom (_, e))   = Just (annedTag e, False)
heapBindingTag (Unfolding (_, v)) = Just (annedTag v, False)
heapBindingTag (Concrete (_, e))  = Just (annedTag e, True)

releaseHeapBindingDeeds :: Deeds -> HeapBinding -> Deeds
releaseHeapBindingDeeds deeds = maybe deeds (releaseTagDeeds deeds) . heapBindingTag

releaseTagDeeds :: Deeds -> (Tag, Bool) -> Deeds
releaseTagDeeds deeds (tg, True)  = releaseDeedDeep deeds tg
releaseTagDeeds deeds (_,  False) = deeds

releasePureHeapDeeds :: Deeds -> PureHeap -> Deeds
releasePureHeapDeeds = M.fold (flip releaseHeapBindingDeeds)

releaseStateDeed :: Deeds -> (Heap, Stack, In (Anned a)) -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> releaseDeedDeep deeds (tag kf))
           (releasePureHeapDeeds (releaseDeedDeep deeds (annedTag e)) h)
           k
