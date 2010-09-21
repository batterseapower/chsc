#include "../Prelude.hs"

safer x d q = x `neq'Int` q && x `neq'Int` q+d && x `neq'Int` q-d
