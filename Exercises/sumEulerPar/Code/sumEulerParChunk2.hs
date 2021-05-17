module Main(main) where

import System.Environment
import System.IO
import Control.Parallel
import Control.Parallel.Strategies
import Control.DeepSeq


hcf :: Int -> Int -> Int
hcf _ 0 = 0
hcf 0 _ = 0
hcf a b | (rem (max a b) (min a b))==0 = min a b
        | a>b = hcf b (rem a b)
        | a<=b = hcf a (rem b a)


relprime :: Int -> Int -> Bool
relprime a b = (hcf a b)==1

euler :: Int -> Int
euler n = length [x | x <- [1..(n-1)], relprime x n]


sumTotient :: Int -> Int -> Int
sumTotient lower upper | lower >= upper = euler upper 
                       | lower < upper = euler lower + (sumTotient (lower+1) upper)


balancedChunk :: [Int] -> Int -> [[Int]] -> [Int] -> [[Int]]
balancedChunk [] _ res tempList  = (tempList:res)
balancedChunk l1 max res tempList | sum tempList >= max = balancedChunk l1 max (tempList:res) []
                                  | sum tempList < max = balancedChunk (tail l1) max res ((head l1):tempList) 



sumTotientList :: [Int] -> Int
sumTotientList xs = sum (map euler xs)

sumTotientChunk :: Int -> Int -> Int -> Int
sumTotientChunk lower upper size = sum (parMap rdeepseq sumTotientList (balancedChunk [lower..upper] (size*upper) [] []))



main = do args <- getArgs
          let 
            lower = read (args!!0) :: Int -- lower limit of the interval
            upper = read (args!!1) :: Int -- upper limit of the interval
            cluster = read (args!!2) :: Int
          hPutStrLn stderr ("Sum of Totients between [" ++ 
                      (show lower) ++ ".." ++ (show upper) ++ "] is " ++ 
                       show (sumTotientChunk lower upper cluster))
