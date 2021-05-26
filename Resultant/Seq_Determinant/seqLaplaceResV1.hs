-- Temporary file
--

detLaplace :: [[Int]] -> Int
detLaplace [[x]] = x
detLaplace (x:xs) = detLaplaceRec 0 (zip x [0..]) xs


detLaplaceRec :: Int -> [(Int,Int)] -> [[Int]] -> Int
detLaplaceRec tot [] m = tot
detLaplaceRec tot (x:xs) m = detLaplaceRec (tot + s*elem*(detLaplace k)) xs m
                             where
                             elem = fst x
                             col = snd x
                             s = if (rem col 2 == 0) then 1 else -1
                             (l1,l2) = splitAt col m
                             k = map (\el -> removeColumn col el) m


removeColumn :: Int -> [Int] -> [Int]
removeColumn c xs = if (length l2 > 0) then l1 ++ (tail l2) else l1
                    where
                    (l1,l2) = splitAt c xs
                    

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
