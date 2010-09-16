data Nat = S Nat | Z
         deriving (Eq, Show)

peanoGt :: Nat -> Nat -> Bool
peanoGt Z     _     = False
peanoGt (S _) Z     = True
peanoGt (S m) (S n) = peanoGt m n

peanoPlus :: Nat -> Nat -> Nat
peanoPlus Z     n = n
peanoPlus (S m) n = S (peanoPlus m n)

fromInt :: Int -> Nat
fromInt 0 = Z
fromInt n = S (fromInt (n - 1))
