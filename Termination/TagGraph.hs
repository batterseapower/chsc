module Termination.TagGraph (
        -- * The TagGraph type
        TagGraph
        
        -- FIXME: the splitter will be broken with this type :(
    ) where

import Termination.Terminate

import Evaluator.Syntax

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


newtype TagGraph = TagGraph { unTagGraph :: IM.IntMap Int }
               deriving (Eq)

instance Pretty TagGraph where
    pPrint = undefined

instance TagCollection TagGraph where
    tr1 <| tr2 = undefined
    
    growingTags = undefined
    
    stateTags = undefined
