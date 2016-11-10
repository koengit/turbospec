module Zip where

import Prelude hiding ( zip, length, rev, (++) )

data Nat = Z | S Nat
 deriving ( Eq )

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

zip :: [a] -> [b] -> [(a,b)]
zip []     _      = []
zip _      []     = []
zip (x:xs) (y:ys) = (x,y) : zip xs ys

prop_ZipRevLength xs ys =
  length (zip xs (rev ys)) == length (zip xs ys)

