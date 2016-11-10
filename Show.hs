module Show where

import Prelude hiding ( Show(..) )

data Expr = Add Expr Expr | Var
 deriving Eq 

data C = Open | X | Plus | Close
 deriving Eq 

parse :: [C] -> Maybe (Expr, [C])
parse (Open : cs) =
  case parse cs of
    Just (a, Close : cs') -> Just (a, cs')
    _                     -> Nothing

parse (X : cs) =
  Just (Var, cs)

parse _ =
   Nothing

show :: Expr -> [C]
show (Add a b) = [Open] ++ show a ++ [Plus] ++ show b ++ [Close]
show Var       = [X]

prop_ParseShow x =
  parse (show x) == Just (x, [])

