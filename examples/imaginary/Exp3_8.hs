#include "../Prelude.hs"

data Nat = Z | S Nat deriving (Eq,Ord, Show {-was:Text-})
