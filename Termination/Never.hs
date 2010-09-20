module Termination.Never (
        -- * The Never type
        Never
    ) where

import Termination.Terminate

import Utilities


data Never = Never

instance Pretty Never where
    pPrint Never = text "{never terminate}"

instance TagCollection Never where
    Never <| Never = Nothing
    
    stateTags _ = Never
