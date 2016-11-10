module Insert where

--import qualified Prelude

insert :: Ord a => a -> [a] -> [a]
insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys

sort :: Ord a => [a] -> [a]
sort []     = []
sort (x:xs) = insert x (sort xs)

ordered :: Ord a => [a] -> Bool
ordered []       = True
ordered [x]      = True
ordered (x:y:xs) = x <= y && ordered (y:xs)

prop_Prop1 xs = ordered (sort xs)

-- please don't use ordered as a function
prop_Prop2 xs = sort (sort xs) == sort xs

