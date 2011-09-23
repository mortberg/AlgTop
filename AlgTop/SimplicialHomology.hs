module AlgTop.SimplicialHomology
  ( diff
  , incidenceMatrix, propIncidenceMatrix
  , homology
  )  where

import Test.QuickCheck
import Data.Function
import Data.List

import AlgTop.SimplicialComplex
import Algebra.Z
import Algebra.SNF_SparseF2

-- Face operators:
faceOp :: Int -> Simplex a -> Simplex a
faceOp i xs | 0 <= i && i < length xs = take i xs ++ drop (i+1) xs
            | otherwise               = error "faceOp: Index out of bounds"

propFaceOp :: Int -> Simplex Z -> Property
propFaceOp i xs = n >= 1 ==> length (faceOp (i `mod` n) xs) == n-1
  where n = length xs

-- Boundary homomorphism (also called differentials):
-- \sum_[i..n] (-1)^i (faceOp i xs)
-- d_n : C_n -> C_n-1, so we get chain:
-- C2 -> C1 -> C0 -> 0
--    d2    d1    d0 = 0
-- Where C1 = 1-simplexes = lists of length 2
--       C0 = 0-simplexes = lists of length 1
diff :: Ord a => Simplex a -> [(Z,Simplex a)]
diff xs | length xs >= 1 = [ ((-1)^i,faceOp i xs) | i <- [0..length xs-1] ]
        | otherwise      = []

-- | Compute n:th incidence matrix of a simplicial complex.
incidenceMatrix :: Ord a => Int -> SC a -> [[Z]]
incidenceMatrix 0 _  = []
incidenceMatrix n xs = incMat (simplexes n xs) (simplexes (n-1) xs)

-- Take a n-simplex and a n-1-simplex and compute the incidence matrix
incMat :: Ord a => [Simplex a] -> [Simplex a] -> [[Z]]
incMat xs ys = transpose [ mat (sortBy (compare `on` snd) (diff x)) ys
                         | x <- xs ]
  where
  mat xs []             = []
  mat [] xs             = replicate (length xs) 0
  mat ((i,d):ds) (x:xs) | x == d    = i : mat ds xs
                        | otherwise = 0 : mat ((i,d):ds) xs

-- | Check that incidence matrices are chain maps.
propIncidenceMatrix :: Int -> SC Z -> Property
propIncidenceMatrix n xs =
  n > 0 ==> allZero (incidenceMatrix n xs `mult` incidenceMatrix (n-1) xs)

mult :: [[Z]] -> [[Z]] -> [[Z]]
mult xs ys = [ [ sum (zipWith (*) x y) | y <- transpose ys ] | x <- xs ]

allZero :: [[Z]] -> Bool
allZero = all (==0) . concat

-- | Compute the n:th homology group of a simplicial complex.
homology :: Ord a => Int -> SC a -> Int
homology n xs =
  let f = length $ simplexes n xs
      k = inv' $ map (map (abs . fromInteger)) $ incidenceMatrix n xs
      m = inv' $ map (map (abs . fromInteger)) $ incidenceMatrix (n+1) xs
  in if n == 0 then f - m else f - k - m
    where
    inv' [] = 0
    inv' xs = inv $ toMat xs
