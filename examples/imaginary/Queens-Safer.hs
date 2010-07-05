#include "../Prelude.hs"

safer x d q = x /= q && x /= q+d && x /= q-d
