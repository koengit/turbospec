module Swap where

swap :: Eq a => a -> a -> [a] -> [a]
swap x y []     = []
swap x y (z:zs) = (if z == x then y else if z == y then x else z) : swap x y zs

member :: Eq a => a -> [a] -> Bool
member x []     = False
member x (y:ys) = x == y || member x ys

prop_Swap x y z zs =
  z `member` zs == z `member` swap x y zs

