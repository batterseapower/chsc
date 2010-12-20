module Termination.TagBag (
        embedWithTagBags
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


type TagBag = M.Map TagSet Nat

embedWithTagBags :: WQO State Generaliser
embedWithTagBags = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ natsWeak) -- TODO: have a version where I replace weakManyNat with (zippable nat)
  where
    -- NB: this is stronger than 
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagBag)", M.map heapBindingTagBag h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (focusedTermTag' e)
      where
        heapBindingTagBag :: HeapBinding -> TagBag
        heapBindingTagBag = maybe (mkTagBag []) (tagTagBag . pureHeapBindingTag') . heapBindingTag
          
        pureHeapTagBag :: PureHeap -> TagBag
        pureHeapTagBag = plusTagBags . map heapBindingTagBag . M.elems
     
        stackTagBag :: Stack -> TagBag
        stackTagBag = mkTagBag . concatMap stackFrameTags'
     
        tagTagBag :: TagSet -> TagBag
        tagTagBag = mkTagBag . return
        
        mkTagBag :: [TagSet] -> TagBag
        mkTagBag = plusTagBags . map (\t -> M.singleton t 1)
        
        plusTagBag :: TagBag -> TagBag -> TagBag
        plusTagBag = M.unionWith (+)
        
        plusTagBags :: [TagBag] -> TagBag
        plusTagBags = foldr plusTagBag M.empty
    
    generaliserFromGrowing :: M.Map TagSet Bool -> Generaliser
    generaliserFromGrowing growing = Generaliser {
          generaliseStackFrame  = \kf   -> any strictly_growing (stackFrameTags' kf),
          generaliseHeapBinding = \_ hb -> maybe False (strictly_growing . pureHeapBindingTag') $ heapBindingTag hb
        }
      where strictly_growing tg = M.findWithDefault False tg growing


pureHeapBindingTag' :: TagSet -> TagSet
pureHeapBindingTag' = IS.map (injectTag 5)

stackFrameTags' :: StackFrame -> [TagSet]
stackFrameTags' = map (IS.map (injectTag 3)) . stackFrameTags

focusedTermTag' :: AnnedTerm -> TagSet
focusedTermTag' = IS.map (injectTag 2) . annedTag
