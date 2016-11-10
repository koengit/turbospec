module Main where

import Data.List
import Data.Dynamic
import Data.Maybe
import qualified Data.Set as S
import Test.QuickCheck
import SAT hiding ( Lit )
import SAT.Unary
import SAT.Val

type Var = (String,Type)

makeVars :: Type -> [String] -> [Var]
makeVars t xs = [ (x,t) | x <- xs ] ++ [ (x++show i,t) | i <- [1..], x <- xs ]

data Type
  = Type
  { tname :: String
  , gen   :: Gen Dynamic
  , vars  :: [Var]
  , eq    :: Dynamic -> Dynamic -> Bool
  }

instance Show Type where
  show tp = tname tp

instance Ord Type where
  p `compare` q = tname p `compare` tname q

instance Eq Type where
  a == b = a `compare` b == EQ

tBool :: Type
tBool = Type "Bool" (toDyn `fmap` (arbitrary :: Gen Bool)) (makeVars tBool ["B"])
        (\x y -> fromDyn x (undefined :: Bool) == fromDyn y (undefined :: Bool))

tNat :: Type
tNat = Type "Nat" (toDyn `fmap` (arbitrary `suchThat` (>=0) :: Gen Nat)) (makeVars tNat ["N","M"]) 
       (\x y -> fromDyn x (undefined :: Nat) == fromDyn y (undefined :: Nat))

tListNat :: Type
tListNat = Type "[Nat]" (toDyn `fmap` (listOf (arbitrary `suchThat` (>=0)) :: Gen [Nat])) (makeVars tListNat ["Ns","Ms"])
           (\x y -> fromDyn x (undefined :: [Nat]) == fromDyn y (undefined :: [Nat]))

data Fun
  = Fun
  { name   :: String
  , args   :: [Type]
  , result :: Type
  , app    :: [Dynamic] -> Dynamic
  }

instance Show Fun where
  show f = name f

fun1 :: (Typeable a, Typeable b) => (a -> b) -> [Dynamic] -> Dynamic
fun1 f [x] = toDyn (f (fromDyn x undefined))

fun2 :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> [Dynamic] -> Dynamic
fun2 f [x,y] = toDyn (f (fromDyn x undefined) (fromDyn y undefined))

type Nat = Int

f_insert :: Fun
f_insert = Fun "insert" [tNat,tListNat] tListNat (fun2 (insert :: Nat -> [Nat] -> [Nat]))

f_sort :: Fun
f_sort = Fun "sort" [tListNat] tListNat (fun1 (sort :: [Nat] -> [Nat]))

instance Ord Fun where
  f `compare` g = name f `compare` name g

instance Eq Fun where
  a == b = a `compare` b == EQ

type Sig = [Fun]

data Lit
  = (Fun,[Var]) :/=:  Var
  | (Fun,[Var]) :<=>: Bool
  | Var         :=:   Var

instance Show Lit where
  show ((f,xs):/=:y)  = show f ++ "(" ++ intercalate "," [ x | (x,_) <- xs] ++ ")!=" ++ fst y
  show ((p,xs):<=>:b) = (if b then "" else "~") ++ show p ++ "(" ++ intercalate "," [ x | (x,_) <- xs] ++ ")"
  show (x :=: y)      = fst x ++ "=" ++ fst y

instance Ord Lit where
  (x:=:y)        `compare` (v:=:w)        = (x,y)    `compare` (v,w)
  (x:=:y)        `compare` _              = LT
  _              `compare` (v:=:w)        = GT
  ((f,xs):/=:x)  `compare` ((g,ys):/=:y)  = (f,xs,x) `compare` (g,ys,y)
  ((f,xs):<=>:a) `compare` ((g,ys):<=>:b) = (f,xs,a) `compare` (g,ys,b)
  ((f,xs):/=:x)  `compare` ((g,ys):<=>:b) = f        `compare` g
  ((f,xs):<=>:a) `compare` ((g,ys):/=:y)  = f        `compare` g

instance Eq Lit where
  a == b = a `compare` b == EQ

type Sub = [(Var,Dynamic)]

eval :: Sub -> Lit -> Bool
eval sub ((f,xs):/=:y@(_,t)) =
  not $ eq t (app f [ a | x <- xs, Just a <- [lookup x sub] ])
             (fromJust (lookup y sub))

eval sub ((p,xs):<=>:b) =
  fromDyn (app p [ a | x <- xs, Just a <- [lookup x sub] ])
          (undefined :: Bool)
          == b

eval sub (x:=:y@(_,t)) =
  eq t (fromJust (lookup x sub)) (fromJust (lookup y sub))

literals :: Int -> Sig -> [Lit]
literals k funs =
  [ (f,xs) :/=: y
  | f  <- funs
  , result f /= tBool
  , xs <- cross [ take k (vars t) | t <- args f ]
  , y  <- take k (vars (result f))
  ] ++
  [ (p,xs) :<=>: b
  | p <- funs
  , result p == tBool
  , xs <- cross [ take k (vars t) | t <- args p ]
  , b  <- [False,True]
  ] ++
  [ x :=: y
  | t <- types
  , x <- take k (vars t)
  , y <- take k (vars t)
  , x < y 
  ]
 where
  types = map head . group . sort $
          [ t
          | f <- funs
          , t <- args f ++ [result f]
          ]

cross :: [[a]] -> [[a]]
cross []       = [[]]
cross (xs:xss) = [ y:ys | y <- xs, ys <- cross xss ]

vec :: Lit -> [Var]
vec ((_,xs) :/=:  y) = xs ++ [y]
vec ((_,xs) :<=>: _) = xs
vec (x      :=: y)   = [x,y]

pre :: Type -> Lit -> Maybe Var
pre typ lit
  | null xs   = Nothing
  | otherwise = gap xs (reverse (takeWhile (/=x) (vars typ)))
 where
  xs = nub [ x | x@(_,t) <- vec lit, t == typ ]
  x  = maxi (vars typ) xs
  
  maxi _      [x] = x
  maxi (y:ys) xs  = maxi ys (filter (/=y) xs)

  gap have []          = Nothing
  gap have (w:want)
    | w `notElem` have = Just w
    | otherwise        = gap have want

type Model = ([(Fun,[Int],Int)],[(Fun,[Int],Bool)])

speculate :: [Lit] -> Model -> IO (Maybe [Lit])
speculate lits (fmod,pmod) =
  withNewSolver $ \s ->
    do ls <- sequence [ newLit s | l <- lits ]
       let tab = lits `zip` ls
       putStrLn ("-- " ++ show (length ls) ++ " literals")
       
       -- no empty clause
       addClause s ls
       
       -- no trivial clauses
       sequence_
         [ addClause s [neg l1, neg l2]
         | ((p,xs):<=>:False,l1) <- tab
         , ((q,ys):<=>:True, l2) <- tab
         , p == q && xs == ys
         ]

       -- no unused definitions
       sequence_
         [ addClause s (neg l1 : [ l2 | (lit2,l2) <- tab, l1 /= l2, y `elem` vec lit2 ])
         | ((_,xs):/=:y,l1) <- tab
         , y `notElem` xs
         ]

       -- removing symmetries
       sequence_
         [ do addClause s (neg l1 : [ l2 | (lit2,l2) <- tab, x `elem` vec lit2 ])
              --print (lit1,[ lit2 | (lit2,l2) <- tab, lit2 < lit1, x `elem` vec lit2 ])
         | (lit1,l1) <- tab
         , typ <- nub [ t | (_,t) <- vec lit1 ]
         , Just x <- [pre typ lit1]
         ]

       -- adding test cases
       let addTests 0 =
             do return ()
           
           addTests i =
             do as <- sequence [ generate (gen t) | (_,t) <- vs ]
                refine S.empty i (vs `zip` as)
           
           refine seen i sub
             | ls `S.member` seen = do addTests (i-1)
             | otherwise          = do --print [ (lit,eval sub lit) | lit <- lits ]
                                       --print [ lit | (lit,l) <- tab, l `elem` ls ]
                                       addClause s ls
                                       ((f,xs):/=:y) <- generate $ elements [ lit | lit@(_:/=:_) <- lits ]
                                       let b = app f [ a | x <- xs, Just a <- [lookup x sub] ]
                                       refine (S.insert ls seen) i
                                              [ if x == y then (y,b) else (x,a) | (x,a) <- sub ]
            where
             ls = [ l | (lit,l) <- tab, eval sub lit ]
           
       addTests 10000
       
       -- adding model constraints
       let tas = [ (t, nub $ [ a
                             | (f,as,b) <- fmod
                             , (a,t') <- (b:as) `zip` (result f:args f)
                             , t' == t
                             ] ++
                             [ a
                             | (p,as,_) <- pmod
                             , (a,t') <- as `zip` args p
                             , t' == t
                             ])
                 | t <- ts
                 ]
       vals <- sequence
         [ newVal s as
         | v@(_,t) <- vs
         , let as:_ = [ as | (t',as) <- tas, t' == t ]
         ]
       let vtab = vs `zip` vals

       sequence_
         [ do cs <- sequence [ newLit s | c <- cases ]
              addClause s (neg l : cs)
              sequence_
                [ addClause s [neg c, v .= a]
                | (c,(as,b)) <- cs `zip` cases
                , (x,a) <- (y:xs) `zip` (b:as)
                , let v:_ = [ v | (x',v) <- vtab, x' == x ]
                ]
         | ((f,xs):/=:y,l) <- tab
         , let cases = [ (as,b) | (f',as,b) <- fmod, f' == f ]
         ]

       sequence_
         [ do cs <- sequence [ newLit s | c <- cases ]
              addClause s (neg l : cs)
              sequence_
                [ addClause s [neg c, v .= a]
                | (c,as) <- cs `zip` cases
                , (x,a) <- xs `zip` as
                , let v:_ = [ v | (x',v) <- vtab, x' == x ]
                ]
         | ((p,xs):<=>:b,l) <- tab
         , let cases = [ as | (p',as,b') <- pmod, p' == p, b' /= b ]
         ]

       -- counting literals
       n <- count s ls

       -- looping
       let loop k | k > 5 =
             do putStrLn "GIVE UP"
                return Nothing
       
           loop k =
             do --putStrLn ("-- solving (k=" ++ show k ++ ")")
                b <- solve s [n .<= k]
                if b then
                  do bs <- sequence [ SAT.modelValue s l | l <- ls ]
                     return (Just [ lit | (lit,True) <- lits `zip` bs ])
                 else
                  do putStrLn ("-- solving (k=" ++ show k ++ ")")
                     loop (k+1)
       loop 1
 where
  vs = nub [ v | lit <- lits, v <- vec lit ]
  ts = nub [ t | (_,t) <- vs ]

