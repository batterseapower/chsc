module Termination.TagGraph (
        -- * The TagGraph type
        TagGraph
    ) where

import Termination.Terminate

import Evaluator.FreeVars
import Evaluator.Syntax

import Utilities

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


data TagGraph = TagGraph { vertices :: IM.IntMap Int, edges :: IM.IntMap IS.IntSet }
               deriving (Eq)

instance Pretty TagGraph where
    pPrint tr = braces $ hsep $ punctuate (text ",") [pPrint tg <+> text "*" <+> pPrint count <+> pPrint (fromMaybe IS.empty (IM.lookup tg (edges tr))) | (tg, count) <- IM.toList (vertices tr)]

instance TagCollection TagGraph where
    tr1 <| tr2 = do
        guard $ tr1 `setEqual` tr2 && cardinality tr1 <= cardinality tr2
        let growing = IM.keysSet (IM.filter (/= 0) (IM.mapMaybe id (combineIntMaps (const Nothing) Just (\i1 i2 -> Just (i2 - i1)) (vertices tr1) (vertices tr2))))
        return $ Generaliser {
            generaliseStackFrame  = \kf       -> all (`IS.member` growing) (stackFrameTags' kf),
            generaliseHeapBinding = \_ (_, e) -> all (`IS.member` growing) (pureHeapBindingTags' e)
          }
    
    stateTags (Heap h _, k, in_e@(_, e)) = traceRender ("stateTags (TagGraph)", graph) $
                                           graph
      where
        graph = pureHeapTagGraph h  
                 `plusTagGraph` stackTagGraph (focusedTermTags' e) k
                 `plusTagGraph` mkTermTagGraph (focusedTermTags' e) in_e
        
        pureHeapTagGraph :: PureHeap -> TagGraph
        pureHeapTagGraph h = plusTagGraphs [mkTagGraph (pureHeapBindingTags' e) (inFreeVars annedTermFreeVars in_e) | in_e@(_, e) <- M.elems h]
        
        stackTagGraph :: [Tag] -> Stack -> TagGraph
        stackTagGraph _         []     = emptyTagGraph
        stackTagGraph focus_tgs (kf:k) = emptyTagGraph { edges = IM.fromList [(kf_tg, IS.singleton focus_tg) | kf_tg <- kf_tgs, focus_tg <- focus_tgs] } -- Binding structure of the stack itself (outer frames refer to inner ones)
                                            `plusTagGraph` mkTagGraph kf_tgs (snd (stackFrameFreeVars kf))                                               -- Binding structure of the stack referring to bound names
                                            `plusTagGraph` stackTagGraph kf_tgs k                                                                        -- Recurse to deal with rest of the stack
          where kf_tgs = stackFrameTags' kf
        
        -- Stores the tags associated with any bound name
        referants = M.map (\(_, e) -> IS.fromList (pureHeapBindingTags' e)) h `M.union` M.fromList [(annee x', IS.fromList (stackFrameTags' kf)) | kf@(Update x') <- k]
        
        -- Find the *tags* referred to from the *names* referred to
        referrerEdges referrer_tgs fvs = M.foldWithKey go IM.empty referants
          where go x referant_tgs edges
                  | x `S.notMember` fvs = edges
                  | otherwise           = foldr (\referrer_tg edges -> IM.insertWith IS.union referrer_tg referant_tgs edges) edges referrer_tgs
        
        mkTermTagGraph e_tgs in_e = mkTagGraph e_tgs (inFreeVars annedTermFreeVars in_e)
        mkTagGraph e_tgs fvs = TagGraph { vertices = IM.unionsWith (+) [IM.singleton e_tg 1 | e_tg <- e_tgs], edges = referrerEdges e_tgs fvs }


pureHeapBindingTags' :: AnnedTerm -> [Tag]
pureHeapBindingTags' = map (injectTag 5) . annedTags

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTags' :: AnnedTerm -> [Tag]
focusedTermTags' = map (injectTag 2) . annedTags


emptyTagGraph :: TagGraph
emptyTagGraph = TagGraph { vertices = IM.empty, edges = IM.empty }

plusTagGraph :: TagGraph -> TagGraph -> TagGraph
plusTagGraph tr1 tr2 = TagGraph { vertices = IM.unionWith (+) (vertices tr1) (vertices tr2), edges = IM.unionWith IS.union (edges tr1) (edges tr2) }

plusTagGraphs :: [TagGraph] -> TagGraph
plusTagGraphs trs = TagGraph { vertices = IM.unionsWith (+) (map vertices trs), edges = IM.unionsWith IS.union (map edges trs) }

cardinality :: TagGraph -> Int
cardinality = IM.fold (+) 0 . vertices

setEqual :: TagGraph -> TagGraph -> Bool
setEqual tr1 tr2 = IM.keysSet (vertices tr1) == IM.keysSet (vertices tr2) && edges tr1 == edges tr2
