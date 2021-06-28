{- 
 <Sequential implementation of univariate polynomial resultant by computing the determinant of the Sylvester matrix.>
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
          hPutStrLn stderr ("Polynomial resultant of " ++ 
                      (show poly1) ++ " and " ++ (show poly2) ++ " is " ++ 
                       show (resultantPoly poly1 poly2))




-------------------------------------------------------
-------------------------------------------------------
---- SYLVESTER MATRIX

-- Create the Sylvester Matrix from 2 univariate polynomials represented as integer lists
--
createSylvMatrix :: [Float] -> [Float] -> [[Float]]
createSylvMatrix p1 p2 = mat1 ++ mat2
                     where
                        n = (length p1) - 1
                        m = (length p2) - 1
                        mat1 = (take m [addZeros p (n+m) i | p <- [p1 | i <- [1..m]], i <- [1..m]])
                        mat2 = (take n [addZeros p (n+m) i | p <- [p2 | i <- [1..n]], i <- [1..n]])


-- Add 0 to the input row given the size of the matrix and its row number in the half matrix
-- 
addZeros :: [Float] -> Int -> Int -> [Float]
addZeros line h k | k <= 1 = line ++ [0 | i <- [1..(h-(length line))]]
                  | k > (h - (length line)) = [0 | i <- [1..(h-(length line))]] ++ line
                  | otherwise = [0 | i <- [1..(k-1)]] ++ line ++ [0 | i <- [1..(h-(length line)-k+1)]]




-------------------------------------------------------
-------------------------------------------------------
---- PLU DECOMPOSITION

-- Compute the matrix U and the determinant P of the PLU decomposition of the input matrix,
-- given the last determinant d and the current pivot column k (initialization: d = 1, k = 0)
--
computeU :: [[Float]] -> Int -> Int -> ([[Float]],Int)
computeU [un] _ d = ([un],d)
computeU (u:us) k d | k >= ((length u - 1)) = ((u:us),d)
                    | (u' !! k) == 0 = computeU (u':us') (k+1) d
                    | otherwise = (u' : mat', d'') 
                    where 
                      (mat, d') = switchPivot (u:us) k
                      u' = head mat
                      us'= tail mat
                      (mat', d'') = (computeUrec [] us' u' k (d*d'))


-- Create 0s under the pivot by Gaussian elimination
--
computeUrec :: [[Float]] -> [[Float]] -> [Float] -> Int -> Int -> ([[Float]],Int)
computeUrec uleft [] _ k d = computeU uleft (k+1) d
computeUrec uleft (uj:uright) uk k d = computeUrec uleft' uright uk k d
                                     where
                                       c =  (uj !! k) / (uk !! k)
                                       uj' = subtractLists uj (map (*c) uk)
                                       uleft' = uleft ++ [uj']


-- Subtract the second list to the first list given in argument
--
subtractLists :: [Float] -> [Float] -> [Float]
subtractLists [] l2 = map (*(-1)) l2
subtractLists l1 [] = l1
subtractLists (x:xs) (y:ys) = (x-y):(subtractLists xs ys)


-- Given the rest of the matrix, if the pivot is zero, swap the pivot with the first
-- row having a non-zero pivot (value of column k)
--
switchPivot :: [[Float]] -> Int -> ([[Float]], Int)
switchPivot (r:rows) k | (r !! k) == 0 = switchPivotRec r rows k []
                       | otherwise = ((r:rows),1)


-- Find the first row with a non-zero pivot and swap it with the first row (r1)
-- If a non-zero pivot exists, negate the determinant d
--
switchPivotRec :: [Float] -> [[Float]] -> Int -> [[Float]] -> ([[Float]], Int)
switchPivotRec r1 [] _ mat = (r1:mat, 1)
switchPivotRec r1 (r:rs) k mat | (r !! k) == 0 = switchPivotRec r1 rs k (mat ++ [r])
                               | otherwise = ((r:mat) ++ (r1:rs), -1)



-------------------------------------------------------
-------------------------------------------------------
---- POLYNOMIAL RESULTANT

-- Given two univariate polynomials, compute their resultant
-- The resultant is the determinant of the PLU decomposition of the Sylvester Matrix
-- det(P) = d, det(L) = 1, det(U) = product of the diagonal of U
--
resultantPoly :: [Float] -> [Float] -> Float
resultantPoly p1 p2 = (diagProd u) * (d')
                     where 
                      (u, d) = (computeU (createSylvMatrix p1 p2) 0 1)
                      d' = fromInteger (toInteger d) :: Float



-- Given a square matrix, compute the product of its diagonal
--
diagProd :: [[Float]] -> Float
diagProd mat = diagProdRec mat 0


diagProdRec :: [[Float]] -> Int -> Float
diagProdRec [] _ = 1
diagProdRec (u:us) i | i >= (length u) = 1
                     | otherwise = (u !! i) * diagProdRec us (i+1) 
