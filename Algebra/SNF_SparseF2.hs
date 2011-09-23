-- | Computation of Smith normal form over F2.
--
-- Given a non-zero mxn matrix A over a F2 it is possible to find invertible 
-- square matrices S and T such that SAT is diagonal and every diagonal 
-- element a_i divides a_{i+1}. 
-- 
-- This is the most efficient version. Works well with sparse matrices over F2.
--
module Algebra.SNF_SparseF2 
  ( Mat(..), Dim(..)
  , fromMat, toMat, convertM, add, mul
  , computeLR, propComputeLR
  , smith, inv, rank
  , computeLRinv, propComputeLRinv
  ) where

import qualified Algebra.SNF_Bezout as M

import Test.QuickCheck

-- Datatype for generating random matrices
data M = M [[Int]]
  deriving (Show,Eq)

-- Maximum dimensiom of random matrices
size :: Int
size = 50

instance Arbitrary M where
  arbitrary = do
    n <- choose (1,size)
    m <- choose (1,size)
    buildM n m
    where
      -- Generate a nxm matrix
      buildM :: Int -> Int -> Gen M
      buildM 0 _ = return $ M []
      buildM n m = do
        xs   <- getN m
        M m  <- buildM (n-1) m
        return $ M (xs:m)

      -- Generate a list with n elements
      getN :: Int -> Gen [Int]
      getN 0 = return []
      getN n = do
        x  <- choose (0,1)
        xs <- getN (n-1)
        return (x:xs)

-- | Datatype of matrices where
--
--   - Id n      = Identity matrix of dimension nxn.
-- 
--   - Zero m n  = mxn zero matrix.
-- 
--   - Row m1 m2 = Row matrix consisting of m1 and m2. 
--
--   - Col m1 m2 = Column matrix consisting of m1 and m2. 
--
data Mat = Id Dim
         | Zero Dim Dim
         | Row Mat Mat
         | Col Mat Mat
  deriving Eq

-- | Dimension as a binary tree to keep track of where the original matrix 
-- has been sliced.  
data Dim = Unit | Plus Dim Dim
  deriving Eq

instance Show Mat where
  show (Id d)       = "Id " ++ show d
  show (Zero d1 d2) = "Zero " ++ show d1 ++ " " ++ show d2
  show (Row m1 m2)  = "Row (" ++ show m1 ++ ") (" ++ show m2 ++ ")"
  show (Col m1 m2)  = "Col (" ++ show m1 ++ ") (" ++ show m2 ++ ")"

eq :: Mat -> Mat -> Bool
eq (Id _)     (Id _)     = True
eq (Zero _ _) (Zero _ _) = True
eq (Col n0 n1) m         = let (m0,m1) = cutCol m
                           in eq n0 m0 && eq n1 m1
eq (Row n0 n1) m         = let (m0,m1) = cutRow m
                           in eq n0 m0 && eq n1 m1
eq _ _                   = error "eq"

instance Arbitrary Mat where
  arbitrary = do M m <- arbitrary
                 return $ toMat m

instance Show Dim where
  show = show . fromDim

instance Arbitrary Dim where
  arbitrary = frequency [ (2,return Unit)
                        , (1,do d1 <- arbitrary
                                d2 <- arbitrary
                                return (Plus d1 d2)) ]

toDim :: Int -> Dim
toDim 1 = Unit
toDim n | n > 1     = Plus Unit (toDim (n-1))
        | otherwise = error "toDim: < 1"

fromDim :: Dim -> Int
fromDim Unit       = 1
fromDim (Plus x y) = fromDim x + fromDim y

-- | Convert a sparse matrix to a list of lists of integers. 
fromMat :: Mat -> [[Int]]
fromMat (Id d)       = identity (fromDim d)
fromMat (Zero d1 d2) = replicate (fromDim d1) (replicate (fromDim d2) 0)
fromMat (Row m1 m2)  = fromMat m1 ++ fromMat m2
fromMat (Col m1 m2)  = zipWith (++) (fromMat m1) (fromMat m2)

identity :: Int -> [[Int]]
identity 0 = []
identity n | n > 0     = (1:replicate (n-1) 0) : map (0:) (identity (n-1))
           | otherwise = error "identity: < 0"

-- | Assumes that the matrix only contain binary values.
toMat :: [[Int]] -> Mat
toMat []     = error "toMat: []"
toMat (x:xs) | all (\y -> length y == length x) xs = splitRow (x:xs)
             | otherwise = error ("toMat: Bad length " ++ show (x:xs))
  where
    splitRow :: [[Int]] -> Mat
    splitRow []    = error "splitRow: []"
    splitRow [x]   = splitCol [x]
    splitRow xs    = let n        = length xs `div` 2  -- div rounds downwards
                         (as,bs)  = splitAt n xs
                     in row (splitCol as) (splitCol bs)

    splitCol :: [[Int]] -> Mat
    splitCol []    = error "splitCol: []"
    splitCol [[0]] = Zero Unit Unit
    splitCol [[1]] = Id Unit
    splitCol xs | all (\x -> length x == 1) xs = splitRow xs
                | otherwise = let n       = length (head xs) `div` 2
                                  (as,bs) = (map (take n) xs,map (drop n) xs)
                              in col (splitRow as) (splitRow bs)

propToFromMat :: M -> Bool
propToFromMat (M m) = m == fromMat (toMat m)

convertM :: M.Mat Integer -> Mat
convertM x = toMat $ map (map (\x -> fromInteger x `mod` 2)) (M.listL x)

-- row and col constructors that guarantee invariants
row :: Mat -> Mat -> Mat
row (Zero d0 d) (Zero d1 _) = Zero (Plus d0 d1) d
row (Col (Id d0) (Zero _ d1)) (Col (Zero _ d0') (Id _))
  | d0 == d0' = Id (Plus d0 d1)
row r0 r1 = Row r0 r1

col :: Mat -> Mat -> Mat
col (Zero d0 d1) (Zero _ d1') = Zero d0 (Plus d1 d1')
col (Row (Id d0) (Zero _ d1)) (Row (Zero _ d0') (Id _))
  | d0 == d0' = Id (Plus d0 d1)
col r0 r1 = Col r0 r1

-- Transposition
transpose :: Mat -> Mat
transpose (Zero d0 d1) = Zero d1 d0
transpose (Id d)       = Id d
transpose (Row m0 m1)  = col (transpose m0) (transpose m1)
transpose (Col m0 m1)  = row (transpose m0) (transpose m1)

propTranspose :: Mat -> Bool
propTranspose m = transpose (transpose m) == m

-- Cutting
cutRow :: Mat -> (Mat,Mat)
cutRow (Zero (Plus d0 d1) e) = (Zero d0 e,Zero d1 e)
cutRow (Id (Plus d0 d1))     = (col (Id d0) (Zero d0 d1),col (Zero d1 d0) (Id d1))
cutRow (Row m0 m1)           = (m0,m1)
cutRow (Col m0 m1)           = let (a,b) = cutRow m0
                                   (c,d) = cutRow m1
                               in (col a c,col b d)
cutRow m                     = error ("cutRow: " ++ show m)


cutCol :: Mat -> (Mat,Mat)
cutCol (Zero d (Plus d0 d1)) = (Zero d d0,Zero d d1)
cutCol (Id (Plus d0 d1))     = (row (Id d0) (Zero d1 d0),row (Zero d0 d1) (Id d1))
cutCol (Col m0 m1)           = (m0,m1)
cutCol (Row m0 m1)           = let (a,b) = cutCol m0
                                   (c,d) = cutCol m1
                               in (row a c,row b d)

-- Dimension
dim :: Mat -> (Dim,Dim)
dim (Zero d0 d1) = (d0,d1)
dim (Id d)       = (d,d)
dim (Row m0 m1)  = let (d0,e) = dim m0
                       (d1,_) = dim m1
                   in (Plus d0 d1,e)
dim (Col m0 m1)  = let (d,e0) = dim m0
                       (_,e1) = dim m1
                   in (d,Plus e0 e1)

propDim :: Mat -> Bool
propDim m = let m'      = fromMat m
                (d0,d1) = dim m
            in (length m',length (head m')) == (fromDim d0,fromDim d1)

-- | Addition.
add :: Mat -> Mat -> Mat
add (Zero _ _) n  = n
add m (Zero _ _)  = m
add (Id d) (Id _) = Zero d d
add (Row m0 m1) n = let (n0,n1) = cutRow n
                    in row (m0 `add` n0) (m1 `add` n1)
add (Col m0 m1) n = let (n0,n1) = cutCol n
                    in col (m0 `add` n0) (m1 `add` n1)
add m n           = add n m

isZero :: Mat -> Bool
isZero (Zero _ _) = True
isZero _          = False

propAddZero :: Mat -> Bool
propAddZero m = isZero (add m m)

-- | Multiplication. 
mul :: Mat -> Mat -> Mat
mul (Id _) m       = m
mul m (Id _)       = m
mul (Zero d0 d1) m = let (_,e) = dim m
                     in Zero d0 e
mul m (Zero d0 d1) = let (e,_) = dim m
                     in Zero e d1
mul (Col m0 m1) n  = let (n0,n1) = cutRow n
                     in (m0 `mul` n0) `add` (m1 `mul` n1)
mul (Row m0 m1) n  = row (m0 `mul` n) (m1 `mul` n)

propMulIdRight :: Mat -> Bool
propMulIdRight m = let (d,e) = dim m
                   in m == (m `mul` Id e)

propMulZeroRight :: Mat -> Bool
propMulZeroRight m = let (d,e) = dim m
                     in isZero (m `mul` Zero e e)

-- (m0 m1) * swap d0 d1 = (m1 m0)
swapCol :: Dim -> Dim -> Mat
swapCol d0 d1 = col (row (Zero d0 d1) (Id d1)) (row (Id d0) (Zero d1 d0))

isCol :: Mat -> Bool
isCol (Col _ _) = True
isCol _         = False

propSwapCol :: Mat -> Property
propSwapCol m = isCol m ==> case m of
  Col m0 m1 -> let (_,d0) = dim m0
                   (_,d1) = dim m1
               in (m `mul` swapCol d0 d1) == col m1 m0

-- (m0 m1) m2 = m0 (m1 m2)
assocr :: Dim -> Dim -> Dim -> Mat
assocr d0 d1 d2 = col c0 c1
  where
    c0 = row (row (Id d0) (Zero d1 d0)) (Zero d2 d0)
    c1 = col c2 c3
    c2 = row (row (Zero d0 d1) (Id d1)) (Zero d2 d1)
    c3 = row (Zero (Plus d0 d1) d2) (Id d2)

-- quickCheckWith stdArgs{maxDiscard=10000} propAssocr
propAssocr :: Mat -> Property
propAssocr m = test m ==> case m of
  (Col (Col m0 m1) m2) ->
    let (_,d0) = dim m0
        (_,d1) = dim m1
        (_,d2) = dim m2
    in (col (col m0 m1) m2) `mul` assocr d0 d1 d2 == col m0 (col m1 m2)
  where
    test (Col (Col _ _) _) = True
    test _ = False

-- m0 (m1 m2) = (m0 m1) m2
assocl :: Dim -> Dim -> Dim -> Mat
assocl d0 d1 d2 = col c0 c1
  where
    c0 = col (row (Id d0) (Zero (Plus d1 d2) d0)) (row (Zero d0 d1) (row (Id d1) (Zero d2 d1)))
    c1 = row (Zero d0 d2) (row (Zero d1 d2) (Id d2))

propAssocl :: Mat -> Property
propAssocl m = test m ==> case m of
  (Col m0 (Col m1 m2)) ->
    let (_,d0) = dim m0
        (_,d1) = dim m1
        (_,d2) = dim m2
    in (col m0 (col m1 m2)) `mul` assocl d0 d1 d2 == col (col m0 m1) m2
  where
    test (Col _ (Col _ _)) = True
    test _ = False

-- (m0 (m1 m2)) * aswap d0 d1 d2 = (m1 (m0 m2))
aswap :: Dim -> Dim -> Dim -> Mat
aswap d0 d1 d2 = row r0 r1
  where
    r0 = col (Zero d0 d1) (col (Id d0) (Zero d0 d2))
    r1 = col c0 c1
    c0 = row (Id d1) (Zero d2 d1)
    c1 = row (Zero d1 (Plus d0 d2)) (col (Zero d2 d0) (Id d2))

propASwap :: Mat -> Property
propASwap m = test m ==> case m of
  (Col m0 (Col m1 m2)) ->
    let (_,d0) = dim m0
        (_,d1) = dim m1
        (_,d2) = dim m2
    in (col m0 (col m1 m2)) `mul` aswap d0 d1 d2 == col m1 (col m0 m2)
  where
    test (Col _ (Col _ _)) = True
    test _ = False

-- Normalize by: ((1 0) 0)^T = ((1 0)^T 0)
norm :: Mat -> Mat
norm (Row (Col (Id d) (Zero _ d0)) (Zero d1 _)) =
  col (row (Id d) (Zero d1 d)) (Zero (Plus d d1) d0)
norm m = m

-- Given d and m return:
--   (1 m)
--   (0 1)
upperTriangle :: Dim -> Dim -> Mat -> Mat
upperTriangle d d1 m = col (row (Id d) (Zero d1 d)) (row m (Id d1))

-- | Compute L, R and m such that: LmR = (1_d 0)^T 0.
computeLR :: Mat -> (Mat,Mat,Mat)
computeLR (Id d)               = (Id d,Id d,Id d)
computeLR (Zero d0 d1)         = (Id d0,Id d1,Zero d0 d1)
computeLR m@(Row _ _)          = let (l,r,a) = computeLR (transpose m)
                                 in (transpose r, transpose l, norm (transpose a))
computeLR (Col (Zero d d0) m1) = let (_,d1)  = dim m1
                                     (l,r,a) = computeLR (col m1 (Zero d d0))
                                 in (l,swapCol d0 d1 `mul` r,a)
computeLR (Col m0 m1) =
  let (l0,r0,a0) = computeLR m0
      (d0,f0)    = dim r0
      (_,d1)     = dim m1
      r1         = col (row r0 (Zero d1 f0)) (row (Zero d0 d1) (Id d1))
      (l',r',a') = clr a0 (l0 `mul` m1)
  in (l' `mul` l0, r1 `mul` r', a')
  where
    clr :: Mat -> Mat -> (Mat,Mat,Mat)
    clr (Id d) m = let (_,d1) = dim m
                   in (Id d,upperTriangle d d1 m,col (Id d) (Zero d d1))
    clr (Col (Id d) (Zero _ d0)) m =
      let (_,d1) = dim m
          r      = col (row (Id d) (Zero (Plus d0 d1) d))
                       (row (col (Zero d d0) m) (Id (Plus d0 d1)))
      in (Id d,assocr d d0 d1 `mul` r,col (Id d) (Zero d (Plus d0 d1)))
    clr (Row (Id d) (Zero d0 _)) m =
      let (_,d1)     = dim m
          (m0,m1)    = cutRow m
          r0         = upperTriangle d d1 m0
          (l1,r1,a1) = computeLR m1
          (f1,_)     = dim l1
          (_,e1)     = dim r1
          l2         = row (col (Id d) (Zero d d0)) (col (Zero f1 d) l1)
          r2         = row (col (Id d) (Zero d e1)) (col (Zero d1 d) r1)
          (l3,r3,a)  = help d a1
      in (l3 `mul` l2,r0 `mul` r2 `mul` r3,a)
    clr (Col s@(Row (Id d) (Zero e _)) (Zero b f)) m =
      let (_,g)   = dim m
          (l,r,a) = clr s (col (Zero b f) m)
      in (l,assocr d f g `mul` r,a)
    clr m _ = error ("clr: " ++ show m)

    help :: Dim -> Mat -> (Mat,Mat,Mat)
    help x (Zero d0 d1) = (Id (Plus x d0)
                          ,Id (Plus x d1)
                          ,col (row (Id x) (Zero d0 x)) (Zero (Plus x d0) d1))
    help x (Id e)       = (Id (Plus x e), Id (Plus x e), Id (Plus x e))
    help x (Col (Id e) (Zero _ f1)) = (Id (Plus x e)
                                      ,assocl x e f1
                                      ,col (Id (Plus x e)) (Zero (Plus x e) f1))
    help x (Row (Id f) (Zero e1 _)) = (transpose (assocl x f e1)
                                      ,Id (Plus x f)
                                      ,row (Id (Plus x f)) (Zero e1 (Plus x f)))
    help x (Col (Row (Id d0) (Zero e _)) (Zero _ d1)) =
      (transpose (assocl x d0 e)
      ,assocl x d0 d1
      ,col (row (Id (Plus x d0)) (Zero e (Plus x d0)))
                (Zero (Plus (Plus x d0) e) d1))
    help x d = error ("help: " ++ show x ++ " " ++ show d)

-- | Compute the Smith normal form of a matrix. 
smith :: Mat -> [[Int]]
smith m = fromMat a
  where (_,_,a) = computeLR m

-- | Compute invariant factors.
inv :: Mat -> Int
inv x = case a of
    Id d                 -> fromDim d
    Col (Id d) _         -> fromDim d
    Row (Id d) _         -> fromDim d
    Col (Row (Id d) _) _ -> fromDim d
    Row (Col (Id d) _) _ -> fromDim d
  where (_,_,a) = computeLR x

-- | Compute the rank of the matrix
rank :: Mat -> Int
rank = inv

-- | Specification of computeLR: L * m * R = a. 
propComputeLR :: Mat -> Bool
propComputeLR m = let (l,r,a) = computeLR m
                  in l `mul` m `mul` r `eq` a


-- | Compute (l,linv,r,rinv,a) where linv is the inverse of l, rinv is the 
-- inverse of r and a is the smith normal form of the matrix. 
computeLRinv :: Mat -> (Mat,Mat,Mat,Mat,Mat)
computeLRinv (Id d)               = (Id d,Id d,Id d,Id d,Id d)
computeLRinv (Zero d0 d1)         = (Id d0,Id d0,Id d1,Id d1,Zero d0 d1)
computeLRinv m@(Row _ _)          =
  let (l,linv,r,rinv,a) = computeLRinv (transpose m)
  in (transpose r, transpose rinv, transpose l, transpose linv, norm (transpose a))
computeLRinv (Col (Zero d d0) m1) =
  let (_,d1)  = dim m1
      (l,linv,r,rinv,a) = computeLRinv (col m1 (Zero d d0))
  in (l,linv,swapCol d0 d1 `mul` r,rinv `mul` swapCol d1 d0,a)
computeLRinv (Col m0 m1) =
  let (l0,l0inv,r0,r0inv,a0) = computeLRinv m0
      (d0,f0)    = dim r0
      (_,d1)     = dim m1
      r1         = col (row r0 (Zero d1 f0)) (row (Zero d0 d1) (Id d1))
      r1inv      = row (col r0inv (Zero f0 d1)) (col (Zero d1 d0) (Id d1))
      (l',l'inv,r',r'inv,a') = clr a0 (l0 `mul` m1)
  in (l' `mul` l0, l0inv `mul` l'inv, r1 `mul` r', r'inv `mul` r1inv, a')
  where
    clr :: Mat -> Mat -> (Mat,Mat,Mat,Mat,Mat)
    clr (Id d) m = let (_,d1) = dim m
                   in (Id d
                      ,Id d
                      ,upperTriangle d d1 m
                      ,upperTriangle d d1 m
                      ,col (Id d) (Zero d d1))
    clr (Col (Id d) (Zero _ d0)) m =
      let (_,d1) = dim m
          r      = col (row (Id d) (Zero (Plus d0 d1) d))
                       (row (col (Zero d d0) m) (Id (Plus d0 d1)))
          rinv   = r
      in (Id d
         ,Id d
         ,assocr d d0 d1 `mul` r
         ,rinv `mul` assocl d d0 d1
         ,col (Id d) (Zero d (Plus d0 d1)))
    clr (Row (Id d) (Zero d0 _)) m =
      let (_,d1)     = dim m
          (m0,m1)    = cutRow m
          r0         = upperTriangle d d1 m0
          r0inv      = r0
          (l1,l1inv,r1,r1inv,a1) = computeLRinv m1
          (f1,_)     = dim l1
          (_,e1)     = dim r1
          l2         = row (col (Id d) (Zero d d0)) (col (Zero f1 d) l1)
          l2inv      = col (row (Id d) (Zero d0 d)) (row (Zero d f1) l1inv)
          r2         = row (col (Id d) (Zero d e1)) (col (Zero d1 d) r1)
          r2inv      = col (row (Id d) (Zero e1 d)) (row (Zero d d1) r1inv)
          (l3,l3inv,r3,r3inv,a)  = help d a1
      in (l3 `mul` l2
         ,l2inv `mul` l3inv
         ,r0 `mul` r2 `mul` r3
         ,r3inv `mul` r2inv `mul` r0inv
         ,a)
    clr (Col s@(Row (Id d) (Zero e _)) (Zero b f)) m =
      let (_,g)   = dim m
          (l,linv,r,rinv,a) = clr s (col (Zero b f) m)
      in (l,linv,assocr d f g `mul` r,rinv `mul` assocl d f g,a)
    clr m _ = error ("clr: " ++ show m)

    help :: Dim -> Mat -> (Mat,Mat,Mat,Mat,Mat)
    help x (Zero d0 d1) = (Id (Plus x d0)
                          ,Id (Plus d0 x)
                          ,Id (Plus x d1)
                          ,Id (Plus d1 x)
                          ,col (row (Id x) (Zero d0 x)) (Zero (Plus x d0) d1))
    help x (Id e)       =
      (Id (Plus x e), Id (Plus e x), Id (Plus x e), Id (Plus e x), Id (Plus x e))
    help x (Col (Id e) (Zero _ f1)) = (Id (Plus x e)
                                      ,Id (Plus e x)
                                      ,assocl x e f1
                                      ,assocr x e f1
                                      ,col (Id (Plus x e)) (Zero (Plus x e) f1))
    help x (Row (Id f) (Zero e1 _)) = (transpose (assocl x f e1)
                                      ,transpose (assocr x f e1)
                                      ,Id (Plus x f)
                                      ,Id (Plus f x)
                                      ,row (Id (Plus x f)) (Zero e1 (Plus x f)))
    help x (Col (Row (Id d0) (Zero e _)) (Zero _ d1)) =
      (transpose (assocl x d0 e)
      ,transpose (assocr x d0 e)
      ,assocl x d0 d1
      ,assocr x d0 d1
      ,col (row (Id (Plus x d0)) (Zero e (Plus x d0)))
                (Zero (Plus (Plus x d0) e) d1))
    help x d = error ("help: " ++ show x ++ " " ++ show d)

-- We don't guarantee the identity invariant, but this trick solves it
isIdentity :: Mat -> Bool
isIdentity m = case toMat (fromMat m) of
  Id _ -> True
  _    -> False

propInvL :: Mat -> Bool
propInvL m = let (l,linv,_,_,_) = computeLRinv m
             in isIdentity (l `mul` linv) && isIdentity (linv `mul` l)

propInvR :: Mat -> Bool
propInvR m = let (_,_,r,rinv,_) = computeLRinv m
             in isIdentity (r `mul` rinv) && isIdentity (rinv `mul` r)

-- | Complete specification of computeLRinv.
propComputeLRinv :: Mat -> Bool
propComputeLRinv m = let (l,linv,r,rinv,a) = computeLRinv m
                     in l `mul` m `mul` r `eq` a
                     && linv `mul` a `mul` rinv `eq` m
                     && propInvL m
                     && propInvR m
