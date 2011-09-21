module AlgTop.SimplicialComplex where

import Control.Monad
import Data.List
import Data.Function
import Test.QuickCheck

type Simplex a = [a]

-- | Comparison operator for simplices; follow from the fact that the vertex
-- set has a comparison operator.
compareSimplex :: Ord a => Simplex a -> Simplex a -> Ordering
compareSimplex xs ys | length xs == length ys = compare xs ys
                     | otherwise = compare (length xs) (length ys)

-- | The type of simplicial complexes.
type SC a = [Simplex a]

fromList :: Ord a => [[a]] -> SC a
fromList = sortBy compareSimplex . nub . map (sort . nub)

-- Some convenient list functions
subsets :: [a] -> [[a]]
subsets []     = [[]]
subsets (x:xs) = map (x:) (subsets xs) ++ subsets xs

powerset :: [a] -> [[a]]
powerset = filterM (const [True,False])

subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = and [ x `elem` ys | x <- xs ]

-- | Naive specification of simplicial complexes.
isSC :: Eq a => SC a -> Bool
isSC xss = and [ all (\x -> x `elem` xss) (subsets xs) | xs <- xss ]

isSorted :: Ord a => SC a -> Bool
isSorted = all (\xs -> xs == sort xs && length xs == length (nub xs))

isSortedSC :: Ord a => SC a -> Bool
isSortedSC xss = isSC xss && isSorted xss

-- Some basic algorithms:

-- | Compute n-simplexes of a simplicial complex.
simplexes :: Int -> SC a -> [Simplex a]
simplexes n xs = filter (\x -> length x == n + 1) xs

faces :: Ord a => Simplex a -> [Simplex a]
faces = fromList . subsets

facets :: Ord a => SC a -> [Simplex a]
facets []       = []
facets (xs:xss) = if any (xs `subset`) xss then facets xss else xs : facets xss

propFacetsFaces :: Ord a => Simplex a -> Property
propFacetsFaces xs = length xs <= 10 ==> fromList [xs] == facets (faces xs)

facetsToSC :: Ord a => [Simplex a] -> SC a
facetsToSC = fromList . concatMap faces

propFacets :: SC Integer -> Property
propFacets xss = isSC xss ==> facetsToSC (facets xss) == xss

-- Horribly slow specification...
propFacetsToSC :: [Simplex Integer] -> Bool
propFacetsToSC = isSC . facetsToSC

-- | Compute the associated simplicial complex from a set of simplexes.
associatedSC :: Ord a => [Simplex a] -> SC a
associatedSC = fromList . concatMap powerset

propAssociatedSC :: [Simplex Integer] -> Property
propAssociatedSC xs = all (\x -> length x <= 10) xs ==> isSC (associatedSC xs)
