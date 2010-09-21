#include "Prelude.hs"

root = ()

tests = [
   (0 `eq'Int` 1, False), (1 `eq'Int` 1, True),
   (0 `neq'Int` 1, True), (1 `neq'Int` 1, False),
   (1 `add'Int` 2, 3),
   (3 `subtract'Int` 2, 1),
   (3 * 2, 6),
   (3 `div'Int` 2, 1), (4 `div'Int` 2, 2),
   (1 `lte'Int` 2, True), (2 `lte'Int` 2, True),
   (1`lt'Int`2, True), (2`lt'Int`2, False),
   (2 `gteq'Int` 2, True), (1 `gteq'Int` 2, False),
   (3 `gt'Int` 2, True), (2 `gt'Int` 2, False),
   (negate'Int (negate'Int 3), 3), (negate'Int 3 `neq'Int` 3, True),
   (signum'Int 4, 1), (signum'Int 0, 0), (signum'Int (negate'Int 2), negate'Int 1),
   (abs'Int 3, 3), (abs'Int (negate'Int 3), 3),
   (3 `mod` 2, 1), (2 `mod` 4, 2),

   (show 1, "1"), (show (10 `add'Int` 9), "19"),

   (id 3, 3),
   ((Left . Right) 1, Left (Right 1)),
   (Left $ 1, Left 1),

   (not True, False), (not False, True),
   (False && False, False), (True && False, False), (False && True, False), (True && True, True), (False && undefined, False),
   (False || False, False), (True || False, True),  (False || True, True),  (True || True, True), (True || undefined, True),

   (head (1 : 2 : []), 1),
   (tail (1 : 2 : []), 2 : []),

   (length [1, 2, 3], 3),
   (map Left [1, 2, 3], [Left 1, Left 2, Left 3]),
   (concatMap (\x -> [x, x]) [1, 2, 3], [1, 1, 2, 2, 3, 3]),
   (foldr (+) 0 [1, 2, 3], 6),
   (take 0 [1, 2, 3], []), (take 2 [1, 2, 3], [1, 2]),
   ([1, 2] ++ [3, 4], [1, 2, 3, 4]),
   (concat [[1, 2], [3, 4]], [1, 2, 3, 4]),
   (enumFromTo'Int 1 4, [1, 2, 3, 4])
 ]