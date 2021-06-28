{-
 <Sequential implementation of univariate polynomial resultant by computing the determinant 
 of the Sylvester matrix with the Laplace expansion.>

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
            poly1 = read (args!!0) :: [Int] -- first polynomial
            poly2 = read (args!!1) :: [Int] -- second polynomial
          hPutStrLn stderr ("Polynomial resultant of " ++
                      (show poly1) ++ " and " ++ (show poly2) ++ " is " ++
                       show (detLaplace (createSylvMatrix poly1 poly2)))


-------------------------------------------------------
-------------------------------------------------------
---- LAPLACE EXPANSION

-- Compute the determinant of an Integer Matrix thanks to the Laplace expansion
-- The column indices are passed by zipping the first row with the indices
--
detLaplace :: [[Int]] -> Int
detLaplace [[x]] = x
detLaplace [[a,b,c],[d,e,f],[g,h,i]] = a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)
detLaplace (x:xs) = detLaplaceRec 0 (zip x [0..]) xs


-- Add recursively the cofactors of the first row
-- 
detLaplaceRec :: Int -> [(Int,Int)] -> [[Int]] -> Int
detLaplaceRec tot [] m = tot
detLaplaceRec tot (x:xs) m = detLaplaceRec (tot + s*elem*(detLaplace k)) xs m
                             where
                             elem = fst x
                             col = snd x
                             s = if (rem col 2 == 0) then 1 else -1
                             (l1,l2) = splitAt col m
                             k = map (\el -> removeColumn col el) m


-- Given a matrix without its first row, create a submatrix by removing the column with index c
--
removeColumn :: Int -> [Int] -> [Int]
removeColumn c xs = if (length l2 > 0) then l1 ++ (tail l2) else l1
                    where
                    (l1,l2) = splitAt c xs
                    

-------------------------------------------------------
-------------------------------------------------------
---- SYLVESTER MATRIX


-- Create the Sylvester Matrix from 2 univariate polynomials represented as integer lists
--
createSylvMatrix :: [Int] -> [Int] -> [[Int]]
createSylvMatrix p1 p2 = mat1 ++ mat2
                     where
                        n = (length p1) - 1
                        m = (length p2) - 1
                        mat1 = (take m [addZeros p (n+m) i | p <- [p1 | i <- [1..m]], i <- [1..m]])
                        mat2 = (take n [addZeros p (n+m) i | p <- [p2 | i <- [1..n]], i <- [1..n]])


-- Add 0 to the input row given the size of the matrix and its row number in the half matrix
-- 
addZeros :: [Int] -> Int -> Int -> [Int]
addZeros line h k | k <= 1 = line ++ [0 | i <- [1..(h-(length line))]]
                  | k > (h - (length line)) = [0 | i <- [1..(h-(length line))]] ++ line
                  | otherwise = [0 | i <- [1..(k-1)]] ++ line ++ [0 | i <- [1..(h-(length line)-k+1)]]
