---------------------------------------------------------------------------
-- 
-- Parallel NFib
-- Calculate a nfib in parallel using a Naïve divide & conquer paradigm
-- nfib is very similar to the Fibonacci series.
---------------------------------------------------------------------------

module Main where

import System.Environment
import Control.Parallel 
import Control.Parallel.Strategies 
import Control.DeepSeq


main = do args <- getArgs
          let 
            n = read (args!!0) :: Int
          putStrLn("parfib2 " ++ (show n) ++ " = " ++ (show (parfib n)))

parfib :: Int -> Int
parfib 0 = 1
parfib 1 = 1
parfib n = nf1+nf2+1 `using` strat
           where nf1 = parfib (n-1)
                 nf2 = parfib (n-2)
                 strat result = do
                                  rpar nf2 
                                  rseq nf1
                                  return result
