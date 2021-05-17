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



remainder :: [Float] -> [Float] -> [Float]
remainder p1 p2 | (length p1) >= (length p2) = fst (euclideRec p1 p2 [])
                | otherwise = fst (euclideRec p2 p1 [])


euclideRec :: [Float] -> [Float] -> [Float] -> ([Float],[Float])
euclideRec [] b q = ([], q)
euclideRec r b q | (length r) < (length b) = (r, q)
                 | otherwise = euclideRec r' b q'
                 where
                   c = divMonom r b
                   q' = addp q c
                   r' = addp r (map (*(-1)) (multp c b))




addp :: [Float] -> [Float] -> [Float]
addp p1 p2 | (length p1) >= (length p2) = polyAddrec (reverse p1) (reverse p2) []
           | otherwise = polyAddrec (reverse p2) (reverse p1) []


polyAddrec :: [Float] -> [Float] -> [Float] -> [Float]
polyAddrec p1 [] res = rmEmptyCoef (reverse (res ++ p1))
polyAddrec (x:xs) (y:ys) res = polyAddrec xs ys (res ++ [z])
                               where z = x + y



multp :: [Float] -> [Float] -> [Float]
multp p1 p2 = polyMult (reverse p1) p2


polyMult :: [Float] -> [Float] -> [Float]
polyMult [] _ = []
polyMult _ [] = []
polyMult (x:xs) ys = addp (map (*x) ys) ((polyMult (xs) ys) ++ [0])



rmEmptyCoef :: [Float] -> [Float]
rmEmptyCoef [] = []
rmEmptyCoef (x:xs) | (abs x) < 1e-2 = rmEmptyCoef xs
                   | otherwise = (x:xs)



leadingMonom :: [Float] -> [Float]
leadingMonom [] = []
leadingMonom [p] = [p]
leadingMonom (p:ps) = p : [0 | i <- [0..(length ps - 1)]]


divMonom :: [Float] -> [Float] -> [Float]
divMonom [] _ = []
divMonom _ [] = []
divMonom (x:xs) (y:ys) | (length xs) < (length ys) = []
                       | otherwise = (x/y) : [0 | i <- [1..((length xs) - (length ys))]]
