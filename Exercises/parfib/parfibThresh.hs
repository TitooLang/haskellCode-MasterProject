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
	    t = read (args!!1) :: Int
          putStrLn("parfib2threshold " ++ (show n) ++ " = " ++ (show (parfib' n t)))

parfib' :: Int -> Int -> Int
parfib' 0 _ = 1
parfib' 1 _ = 1
parfib' n t 
	| n>t = nf1+nf2+1 `using` strat
        | n<=t = parfib' (n-1) t + parfib'(n-2) t + 1
           where nf1 = parfib' (n-1) t
                 nf2 = parfib' (n-2) t
                 strat result = do
                                  rpar nf2 
                                  rseq nf1
                                  return result

