{- 
 <Sequential implementation of univariate polynomial resultant thanks to a recursive 
 algorithm based on Euclidean division.>
    Copyright (C) 2021  Titouan Langevin
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}


-------------------------------------------------------
-------------------------------------------------------
---- MAIN

import System.Environment
import System.IO

main = do args <- getArgs
          let 
            poly1 = read (args!!0) :: [Float] -- first polynomial
            poly2 = read (args!!1) :: [Float] -- second polynomial
          hPutStrLn stderr ("Polynomial resultant is " ++ 
                       show (resultant poly1 poly2))



-------------------------------------------------------
-------------------------------------------------------
---- RECURSIVE RESULTANT


-- This algorithm is based on the pseudo-code from Antonio Machi 
-- in "Algebra for Symbolic Computation"
--
resultant :: [Float] -> [Float] -> Float
resultant p1 p2 | n > m = (-1)^(m+1) * resultant p2 p1
                | n == 0 = an ^ m
                | r == [] = 0
                | otherwise = an^(m-p) * resultant p1 r
                where
                  n = length p1 - 1
                  m = length p2 - 1
                  an = (head p1)
                  r = remainder p2 p1
                  p = length r - 1



-------------------------------------------------------
-------------------------------------------------------
---- EUCLIDEAN DIVISION


-- Compute the remainder of the division p1/p2
--
remainder :: [Float] -> [Float] -> [Float]
remainder p1 p2 | (length p1) >= (length p2) = fst (euclideRec p1 p2 [])
                | otherwise = fst (euclideRec p2 p1 [])


-- Euclidean division algorithm based on the pseudo-code from Antonio Machi
--
euclideRec :: [Float] -> [Float] -> [Float] -> ([Float],[Float])
euclideRec [] b q = ([], q)
euclideRec r b q | (length r) < (length b) = (r, q)
                 | otherwise = euclideRec r' b q'
                 where
                   c = divMonom r b
                   q' = addp q c
                   r' = addp r (map (*(-1)) (multp c b))



-------------------------------------------------------
-------------------------------------------------------
---- OPERATIONS ON POLYNOMIALS


-- Addition
--
addp :: [Float] -> [Float] -> [Float]
addp p1 p2 | (length p1) >= (length p2) = polyAddrec (reverse p1) (reverse p2) []
           | otherwise = polyAddrec (reverse p2) (reverse p1) []


polyAddrec :: [Float] -> [Float] -> [Float] -> [Float]
polyAddrec p1 [] res = rmEmptyCoef (reverse (res ++ p1))
polyAddrec (x:xs) (y:ys) res = polyAddrec xs ys (res ++ [z])
                               where z = x + y



-- Multiplication
--
multp :: [Float] -> [Float] -> [Float]
multp p1 p2 = polyMult (reverse p1) p2


polyMult :: [Float] -> [Float] -> [Float]
polyMult [] _ = []
polyMult _ [] = []
polyMult (x:xs) ys = addp (map (*x) ys) ((polyMult (xs) ys) ++ [0])



-------------------------------------------------------
-------------------------------------------------------
---- AUXILIARY FUNCTIONS


-- Remove the coefficients of highest degree which are null
-- so that calculating the degree thanks to the length remains consistent
--
rmEmptyCoef :: [Float] -> [Float]
rmEmptyCoef [] = []
rmEmptyCoef (x:xs) | (abs x) < 1e-2 = rmEmptyCoef xs
                   | otherwise = (x:xs)


-- Divide the leading monomials of two polynomials
-- The first polynomial must be of degree greater than the second
--
divMonom :: [Float] -> [Float] -> [Float]
divMonom [] _ = []
divMonom _ [] = []
divMonom (x:xs) (y:ys) | (length xs) < (length ys) = []
                       | otherwise = (x/y) : [0 | i <- [1..((length xs) - (length ys))]]
