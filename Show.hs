module Show where

import Prelude hiding ( Show(..) )

data Expr = Add Expr Expr | Var
 deriving Eq 

data C = Open | X | Plus | Close
 deriving Eq 

atom :: [C] -> Maybe (Expr, [C])
atom (Open : cs) =
  case parse cs of
    Just (a, Close : cs') -> Just (a, cs')
    _                     -> Nothing

atom (X : cs) =
  Just (Var, cs)

atom _ =
   Nothing

parse :: [C] -> Maybe (Expr, [C])
parse cs =
  case atom cs of
    Just (a, cs') ->
      case cs' of
        Plus : cs'' ->
          case parse cs'' of
            Just (b, cs''') -> Just (Add a b, cs''')
            _               -> Just (a, cs')
        _ -> Just (a, cs')
    _ -> Nothing

show :: Expr -> [C]
show (Add a b) = [Open] ++ show a ++ [Plus] ++ show b ++ [Close]
show Var       = [X]

prop_ParseShow x =
  parse (show x) == Just (x, [])

