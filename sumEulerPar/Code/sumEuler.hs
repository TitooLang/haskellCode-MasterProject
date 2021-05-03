module Main(main) where

import System.Environment
import System.IO

hcf :: Integer -> Integer -> Integer
hcf _ 0 = 0
hcf 0 _ = 0
hcf a b | (rem (max a b) (min a b))==0 = min a b
        | a>b = hcf b (rem a b)
        | a<=b = hcf a (rem b a)


relprime :: Integer -> Integer -> Bool
relprime a b = (hcf a b)==1

euler :: Integer -> Int
euler n = length [x | x <- [1..(n-1)], relprime x n]


sumTotient :: Integer -> Integer -> Int
sumTotient lower upper | lower >= upper = euler upper
                       | lower < upper = euler lower + (sumTotient (lower+1) upper)

main = do args <- getArgs
          let 
            lower = read (args!!0) :: Integer -- lower limit of the interval
            upper = read (args!!1) :: Integer -- upper limit of the interval
          hPutStrLn stderr ("Sum of Totients between [" ++ 
                      (show lower) ++ ".." ++ (show upper) ++ "] is " ++ 
                       show (sumTotient lower upper))
