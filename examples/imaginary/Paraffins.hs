import Array

#include "../Prelude.hs"

data Radical = H | C Radical Radical Radical

data Paraffin = BCP Radical Radical | CCP Radical Radical Radical Radical

arrayLookup = (Array.!)
