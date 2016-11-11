module Main where

import System.IO( hFlush, stdout )
import Data.List
import Data.Dynamic
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Test.QuickCheck
import SAT hiding ( Lit )
import SAT.Unary
import SAT.Val
import SAT.Equal

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
tNat = Type "Nat" (toDyn `fmap` (arbitrary `suchThat` (>=0) :: Gen Nat)) (makeVars tNat ["N"]) 
       (\x y -> fromDyn x (undefined :: Nat) == fromDyn y (undefined :: Nat))

tListNat :: Type
tListNat = Type "[Nat]" (toDyn `fmap` (listOf (arbitrary `suchThat` (>=0)) :: Gen [Nat])) (makeVars tListNat ["Ns"])
           (\x y -> fromDyn x (undefined :: [Nat]) == fromDyn y (undefined :: [Nat]))

tA :: Type
tA = Type "A" (toDyn `fmap` (arbitrary :: Gen Int)) (makeVars tA ["X"]) 
       (\x y -> fromDyn x (undefined :: Int) == fromDyn y (undefined :: Int))

tB :: Type
tB = Type "B" (toDyn `fmap` (arbitrary :: Gen Int)) (makeVars tB ["Y"]) 
       (\x y -> fromDyn x (undefined :: Int) == fromDyn y (undefined :: Int))

tAB :: Type
tAB = Type "(A,B)" (toDyn `fmap` (arbitrary :: Gen (Int,Int))) (makeVars tAB ["P"]) 
       (\x y -> fromDyn x (undefined :: (Int,Int)) == fromDyn y (undefined :: (Int,Int)))

tListA :: Type
tListA = Type "[A]" (toDyn `fmap` (listOf arbitrary :: Gen [Int])) (makeVars tListA ["Xs"])
           (\x y -> fromDyn x (undefined :: [Int]) == fromDyn y (undefined :: [Int]))

tListB :: Type
tListB = Type "[B]" (toDyn `fmap` (listOf arbitrary :: Gen [Int])) (makeVars tListB ["Ys"])
           (\x y -> fromDyn x (undefined :: [Int]) == fromDyn y (undefined :: [Int]))

tListAB :: Type
tListAB = Type "[(A,B)]" (toDyn `fmap` (listOf arbitrary :: Gen [(Int,Int)])) (makeVars tListAB ["Ps"])
           (\x y -> fromDyn x (undefined :: [(Int,Int)]) == fromDyn y (undefined :: [(Int,Int)]))

tListAA :: Type
tListAA = Type "[(A,A)]" (toDyn `fmap` (listOf arbitrary :: Gen [(Int,Int)])) (makeVars tListAA ["Ps"])
           (\x y -> fromDyn x (undefined :: [(Int,Int)]) == fromDyn y (undefined :: [(Int,Int)]))

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

fun3 :: (Typeable a, Typeable b, Typeable c, Typeable d) => (a -> b -> c -> d) -> [Dynamic] -> Dynamic
fun3 f [x,y,z] = toDyn (f (fromDyn x undefined) (fromDyn y undefined) (fromDyn z undefined))

type Nat = Int

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

literals :: (Type -> Int) -> Sig -> [Lit]
literals tyNum funs =
  [ (f,xs) :/=: y
  | f  <- funs
  , result f /= tBool
  , xs <- cross [ take (tyNum t) (vars t) | t <- args f ]
  , y  <- take (tyNum (result f)) (vars (result f))
  ] ++
  [ (p,xs) :<=>: b
  | p <- funs
  , result p == tBool
  , xs <- cross [ take (tyNum t) (vars t) | t <- args p ]
  , b  <- [False,True]
  ] ++
  [ x :=: y
  | t <- types
  , (x,i) <- take (tyNum t) (vars t) `zip` [1..]
  , y     <- drop i $ take (tyNum t) (vars t)
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
  | otherwise = gap (takeWhile (/=x) xs) (reverse (takeWhile (/=x) (vars typ)))
 where
  xs = nub [ x | x@(_,t) <- vec lit, t == typ ]
  x  = maxi (vars typ) xs
  
  maxi _      [x] = x
  maxi (y:ys) xs  = maxi ys (filter (/=y) xs)

  gap have []          = Nothing
  gap have (w:want)
    | w `notElem` have = Just w
    | otherwise        = gap (takeWhile (/=w) have) want

(<<) :: Lit -> Lit -> Bool
lit1 << lit2 = prnt lit1 < prnt lit2
 where
  prnt lit@(_:=:_)       = Nothing
  prnt lit@((f,_):/=:_)  = Just (f, norm M.empty 0 (vec lit))
  prnt lit@((p,_):<=>:_) = Just (p, norm M.empty 0 (vec lit))

  norm tab i []     = []
  norm tab i (x:xs) =
    case M.lookup x tab of
      Nothing -> i : norm (M.insert x i tab) (i+1) xs
      Just j  -> j : norm tab i xs

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

       -- no twice definitions
       sequence_
         [ addClause s [neg l1, neg l2]
         | (fxs :/=:x,l1) <- tab
         , (fxs':/=:y,l2) <- tab
         , fxs == fxs'
         , x /= y
         ]

       -- no free variables in equations
       sequence_
         [ do addClause s (neg l1 : [ l2 | (lit2,l2) <- tab, notEq lit2, x `elem` vec lit2 ])
              addClause s (neg l1 : [ l2 | (lit2,l2) <- tab, notEq lit2, y `elem` vec lit2 ])
         | (x:=:y,l1) <- tab
         , let notEq (_:=:_) = False
               notEq _       = True
         ]

       -- removing symmetries
       putStrLn ("-- removing symmetries...")
       sequence_
         [ do putStrLn (show lit1 ++ " --> " ++ fst x)
              addClause s (neg l1 : [ l2 | (lit2,l2) <- tab, l1 /= l2, not (lit1 << lit2), x `elem` vec lit2 ])
         | (lit1,l1) <- tab
         , typ <- nub [ t | (_,t) <- vec lit1 ]
         , Just x <- [pre typ lit1]
         ]

       -- adding test cases
       putStrLn ("-- adding test cases...")
       let tests' seen i j sub | i >= 300 =
             do putStrLn ("(" ++ show (S.size seen) ++ " clauses)")
                return seen
           
           tests' seen i j sub | j >= 5*length lits =
             do tests seen i
           
           tests' seen i j sub =
             do new <- solve s (map neg cl)
                let lits1 = [ lit | (lit@(_:/=:_),True) <- lits `zip` bs ]
                (y,b) <- if not (null lits1) then
                           do ((f,xs):/=:y) <- generate $ elements lits1
                              let b = app f [ a | x <- xs, Just a <- [lookup x sub] ]
                              return (y,b)
                         else
                           do y <- generate $ elements vs
                              b <- generate (resize (i `mod` 100) (gen (snd y)))
                              return (y,b)
                let sub' = [ if x == y then (y,b) else (x,a) | (x,a) <- sub ]     
                if new then
                  do putStr "."
                     hFlush stdout
                     addClause s cl
                     tests' (S.insert cl seen) 0 0 sub'
                 else
                  do tests' seen i (j+1) sub'
            where
             bs = [ eval sub lit | lit <- lits ]
             cl = [ l | (l,True) <- ls `zip` bs ]
           
           tests seen i =
             do putStr "#"
                hFlush stdout
                as <- sequence [ generate (resize (i `mod` 100) (gen t)) | (_,t) <- vs ]
                tests' seen (i+1) 0 (vs `zip` as)
           
       tsts <- tests S.empty 0
       
       -- every speculated clause must be (locally) minimal
       sequence_
         [ do xs <- sequence [ newLit s | c <- cs ]
              addClause s (neg l : xs)
              sequence_
                [ addClause s [neg x, neg l']
                | (x,c) <- xs `zip` cs
                , l' <- c
                , l' /= l
                ]
         | (l,cs) <- M.toList $ M.fromListWith (++)
                     [ (l,[ls])
                     | ls <- S.toList tsts
                     , l <- ls
                     ]
         ]
       
       -- adding model constraints
       putStrLn ("-- adding model constraints...")
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
                 , t /= tBool
                 ] ++
                 [ (tBool, [0,1]) ]
       vals <- sequence
         [ do putStrLn (fst v ++ " = " ++ show as)
              newVal s as
         | v@(_,t) <- vs
         , [as] <- [[ as | (t',as) <- tas, t' == t ]]
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

       sequence_
         [ do notEqualOr s [neg l] a b
         | (x:=:y,l) <- tab
         , [a] <- [[ v | (x',v) <- vtab, x' == x ]]
         , [b] <- [[ v | (y',v) <- vtab, y' == y ]]
         ]

       -- counting literals
       n <- count s ls

       -- looping
       let loop k | k > 10 =
             do putStrLn "GIVE UP"
                return Nothing
       
           loop k =
             do --putStrLn ("-- solving (k=" ++ show k ++ ")")
                b <- solve s [n .<= k]
                if b then
                  do bs <- sequence [ SAT.modelValue s l | l <- ls ]
                     print [ lit | (lit,True) <- lits `zip` bs ]
                     addClause s (map neg [ l | (l,True) <- ls `zip` bs ])
                     --return (Just [ lit | (lit,True) <- lits `zip` bs ])
                     loop k
                 else
                  do putStrLn ("-- solving (k=" ++ show k ++ ")")
                     loop (k+1)
       loop 1
 where
  vs = nub [ v | lit <- lits, v <- vec lit ]
  ts = nub [ t | (_,t) <- vs ]

main1 =
  do c <- speculate (literals tyNum sig) (fmod,pmod)
     print c
 where
  sig = [f_insert,f_sort,f_sorted]

  a = 1
  as = 2
  sort_as = 3
  sort_aas = 4
  aas = 5
  
  fmod = [ (f_sort,[as],sort_as)
         , (f_sort,[aas],sort_aas)
         , (f_insert,[a,sort_as],sort_aas)
         ]
  
  pmod = [ (f_sorted,[sort_as],True)
         , (f_sorted,[sort_aas],False)
         ]

tyNum t | t == tBool    = 2
tyNum t | t == tNat     = 2
tyNum t | t == tA       = 3
tyNum t | t == tB       = 2
tyNum t | t == tAB      = 2
tyNum t | t == tListNat = 2
tyNum t | t == tListA   = 2
tyNum t | t == tListB   = 2
tyNum t | t == tListAB  = 2
tyNum t | t == tListAA  = 2

main2 =
  do c <- speculate (literals tyNum sig) (fmod,pmod)
     print c
 where
  sig = [f_rev,f_zip,f_lenAA,f_lenA]

  as:cs:ras
    :zip_as_cs:zip_as_ras
    :len_as:len':_
    = [1..]

  fmod = [ (f_zip, [as,cs],  zip_as_cs)
         , (f_zip, [as,ras], zip_as_ras)
         
         , (f_rev, [as], ras)
         
         , (f_lenA, [as],  len_as)
         , (f_lenA, [ras], len_as)
         , (f_lenA, [cs],  len_as)
         
         , (f_lenAA, [zip_as_ras], len_as)
         , (f_lenAA, [zip_as_cs],  len')
         ]
  
  pmod = []

main =
  do c <- speculate (literals tyNum sig) (fmod,pmod)
     print c
 where
  sig = [f_memb,f_swap]

  a:b:c:d
   :das:swap_das:_
    = [1..]

  fmod = [ (f_swap, [a,b,das], swap_das)
         ]
  
  pmod = [ (f_memb, [a, das], True)
         , (f_memb, [b, das], True)
         , (f_memb, [c, das], True)
         , (f_memb, [c, swap_das], False)
         ]

f_insert :: Fun
f_insert = Fun "insert" [tA,tListA] tListA (fun2 (insert :: Nat -> [Nat] -> [Nat]))

f_sort :: Fun
f_sort = Fun "sort" [tListA] tListA (fun1 (sort :: [Nat] -> [Nat]))

f_sorted :: Fun
f_sorted = Fun "sorted" [tListA] tBool (fun1 (\xs -> sort xs == (xs :: [Nat])))

f_rev :: Fun
f_rev = Fun "rev" [tListB] tListB (fun1 (reverse :: [Int] -> [Int]))

f_zip :: Fun
f_zip = Fun "zip" [tListA,tListA] tListAA (fun2 (zip :: [Int] -> [Int] -> [(Int,Int)]))

f_lenA :: Fun
f_lenA = Fun "lenA" [tListA] tNat (fun1 (length :: [Int] -> Int))

f_lenB :: Fun
f_lenB = Fun "lenB" [tListB] tNat (fun1 (length :: [Int] -> Int))

f_lenAB :: Fun
f_lenAB = Fun "lenAB" [tListAB] tNat (fun1 (length :: [(Int,Int)] -> Int))

f_lenAA :: Fun
f_lenAA = Fun "lenAA" [tListAA] tNat (fun1 (length :: [(Int,Int)] -> Int))

f_memb :: Fun
f_memb = Fun "memb" [tA,tListA] tBool (fun2 (elem :: Int -> [Int] -> Bool))

f_swap :: Fun
f_swap = Fun "swap" [tA,tA,tListA] tListA (fun3 (swap :: Int -> Int -> [Int] -> [Int]))
 where
  swap x y xs = [ if z == x then y else if z == y then x else z | z <- xs ]


