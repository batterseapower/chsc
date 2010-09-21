#include "Prelude.hs"

root = ()

tests = [
   (0 == 1, False), (1 == 1, True),
   (0 /= 1, True), (1 /= 1, False),
   (1 + 2, 3),
   (3 - 2, 1),
   (3 * 2, 6),
   (3 `div` 2, 1), (4 `div` 2, 2),
   (1 <= 2, True), (2 <= 2, True),
   (1 < 2, True), (2 < 2, False),
   (2 >= 2, True), (1 >= 2, False),
   (3 > 2, True), (2 > 2, False),
   (negate (negate 3), 3), (negate 3 /= 3, True),
   (signum 4, 1), (signum 0, 0), (signum (negate 2), negate 1),
   (abs 3, 3), (abs (negate 3), 3),
   (3 `mod` 2, 1), (2 `mod` 4, 2),

   (show 1, "1"), (show (10 + 9), "19"),

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