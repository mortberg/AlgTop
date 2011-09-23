-- | Computation of Smith normal form over a Bezout domain.
--
-- Given a non-zero mxn matrix A over a Bezout domain it is possible to find
-- invertible square matrices S and T such that SAT is diagonal and every
-- diagonal element a_i divides a_{i+1}.
--
-- This implementation don't bother about sparseness or computing witnesses.
--
{-# LANGUAGE NoMonomorphismRestriction  #-}
module Algebra.SNF_Bezout
  ( Mat(..), toMat
  , listL, listC
  , add, mult
  , smith, inv, rank
  ) where

import Algebra.Structures.IntegralDomain
import Algebra.Structures.BezoutDomain

-- Cons x xs ys m = (x:xs) : (map (\y -> y:) ys) m
data Mat a = Empty | Cons !a ![a] ![a] !(Mat a)
  deriving (Eq,Show)

instance Functor Mat where
  fmap f Empty = Empty
  fmap f (Cons a xs ys m) = Cons (f a) (map f xs) (map f ys) (fmap f m)

toMat :: [[a]] -> Mat a
toMat [] = Empty
toMat ([]:_) = Empty
toMat ((x:xs):xss) = Cons x xs (map head xss) (toMat (map tail xss))

listC :: Mat a -> [[a]]
listC Empty                = []
listC (Cons u ls cs Empty) = [u:cs]
listC (Cons u ls cs m)     = (u:cs) : zipWith (:) ls (listC m)

listL :: Mat a -> [[a]]
listL Empty                = []
listL (Cons u ls cs Empty) = [u:ls]
listL (Cons u ls cs m)     = (u:ls) : zipWith (:) cs (listL m)

zeroes :: Ring a => Int -> [a]
zeroes n = replicate n zero

ident :: Ring a => Int -> Mat a
ident 0 = Empty
ident n = let z = zeroes (n-1)
          in Cons one z z (ident (n-1))

adds :: Ring a => [a] -> [a] -> [a]
adds [] vs         = vs
adds us []         = us
adds (u:us) (v:vs) = (u<+>v) : adds us vs

-- | Addition of matrices.
add :: Ring a => Mat a -> Mat a -> Mat a
add Empty n = n
add m Empty = m
add (Cons u0 ls0 cs0 m0) (Cons u1 ls1 cs1 m1) =
 Cons (u0<+>u1) (adds ls0 ls1) (adds cs0 cs1) (add m0 m1)

-- Multiplication line vector matrix.
multLM :: Ring a => [a] -> Mat a -> [a]
multLM [] _ = []
multLM us m = map (prods us) (listC m)

-- Multiplication matrix column vector.
multMC :: Ring a => Mat a -> [a] -> [a]
multMC _ [] = []
multMC m us = map (prods us) (listL m)

-- Multiplication element vector.
multEV :: Ring a => a -> [a] -> [a]
multEV = map . (<*>)

-- Multiplication of matrices.
prods :: Ring a => [a] -> [a] -> a
prods us vs
  | length us == length vs = sumRing $ zipWith (<*>) us vs
  | otherwise = error "prods"

mults :: Ring a => [a] -> [a] -> Mat a
mults [] _          = Empty
mults _  []         = Empty
mults (u:us) (v:vs) =
  Cons (u<*>v) (map (u<*>) vs) (map (v<*>) us) (mults us vs)

-- | Multiplication of matrices.
mult :: Ring a => Mat a -> Mat a -> Mat a
mult Empty _ = Empty
mult _ Empty = Empty
mult (Cons u0 ls0 cs0 m0) (Cons u1 ls1 cs1 m1) =
  Cons (u0<*>u1 <+> prods ls0 cs1)
       (adds (multEV u0 ls1) (multLM ls0 m1))
       (adds (multEV u1 cs0) (multMC m0 cs1))
       (add  (mults cs0 ls1) (mult m0 m1))

-- Given a column matrix m, computes e such that mult e m is of the form
--    g
--    0
-- where g is the gcd of the column m.
lemV :: (BezoutDomain a, Eq a) => [a] -> (Mat a,a)
lemV []     = (Empty,zero)
lemV [a]    = (Cons one [] [] Empty,a)
lemV (a:as) =
 let (m,b) = lemV as
     n     = length as - 1
     z0    = zeroes n
     z     = zero : z0
     e     = Cons one z z m
     (g,a1,b1,u,v) = bezout a b
 in (mult (Cons u (v:z0) (neg b1:z0) (Cons a1 z0 z0 (ident n))) e,g)

-- Given a line matrix m, lemH m computes f such that mult m f is of the form
--    g 0
-- where g is the gcd of the line m.
-- We reduce this to the function lemV using the transpose function
transpose :: Mat a -> Mat a
transpose Empty            = Empty
transpose (Cons u ls cs m) = Cons u cs ls (transpose m)

lemH :: (BezoutDomain a, Eq a) => [a] -> (Mat a, a)
lemH as = let (m,g) = lemV as
          in (transpose m,g)

-- smith m computes invertible matrices e and f such that mult e (mult m f)
-- is of the form
--
--     g 0
--     0 n
--
-- where g is the gcd of the first line + first column of m
isZero :: (Ring a, Eq a) => [a] -> Bool
isZero = all (==zero)

-- | Compute the Smith normal form of a matrix.
smith :: (BezoutDomain a, Eq a) => Mat a -> Mat a
smith Empty              = Empty
smith m@(Cons u ls cs _) =
  if isZero cs
     then if isZero ls
             then m
             else let (f,_) = lemH (u:ls)
                  in smith (mult m f)
     else let (e,_) = lemV (u:cs)
          in smith (mult e m)

-- | Compute invariant factors of the matrix.
inv :: (BezoutDomain a, Eq a) => Mat a -> [a]
inv Empty = []
inv m     = let Cons g _ _ m1 = smith m
            in if g == zero then inv m1 else g : inv m1

-- | Compute the rank of the matrix
rank :: (BezoutDomain a, Eq a) => Mat a -> Int
rank = length . inv
