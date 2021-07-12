import System.Random

data MulPoly = Cons Int | Poly [MulPoly] deriving (Show)

-- ADDITION
--

addPoly p1 p2 p = rmZeros (polyMod (addPolyM p1 p2) p)

addPolyM :: MulPoly -> MulPoly -> MulPoly
addPolyM (Cons a) (Cons b) = Cons (a+b)
addPolyM (Cons a) (Poly p) | length p == 0 = Cons a
                           | a == 0 = Poly p
                           | otherwise = Poly ((addPolyM (Cons a) (head p)) : (tail p))
addPolyM (Poly p) (Cons b) = addPolyM (Cons b) (Poly p)
addPolyM (Poly p1) (Poly p2) | length p1 == 0 = Poly p2
                             | length p2 == 0 = Poly p1
                             | length p1 == 1 = Poly ((addPolyM (head p1) (head p2)) : tail p2)
                             | length p2 == 1 = Poly ((addPolyM (head p1) (head p2)) : tail p1)
                             | otherwise = Poly ((addPolyM (head p1) (head p2)) : p3)
                             where p3 = addPolyMRec (tail p1) (tail p2)


addPolyMRec :: [MulPoly] -> [MulPoly] -> [MulPoly]
addPolyMRec [] p = p
addPolyMRec p [] = p
addPolyMRec (x:xs) (y:ys) = (addPolyM x y) : (addPolyMRec xs ys)




-- MULTIPLICATION
--

multPoly p1 p2 p = rmZeros (polyMod (multPolyM p1 p2) p)


multPolyM :: MulPoly -> MulPoly -> MulPoly
multPolyM (Cons a) (Cons b) = Cons (a*b)
multPolyM (Cons a) (Poly p) | (length p == 0 || a == 0) = Cons 0
                            | otherwise = Poly (map (\el -> multPolyM (Cons a) el) p)
multPolyM (Poly p) (Cons a) = multPolyM (Cons a) (Poly p)
multPolyM (Poly p1) (Poly p2) | length p1 == 0 = Cons 0
                              | length p2 == 0 = Cons 0
                              | otherwise = foldr addPolyM (Cons 0) (multPolyMRec p1 p2)



multPolyMAux :: MulPoly -> MulPoly -> MulPoly
multPolyMAux (Cons a) (Poly p) = multPolyM (Cons a) (Poly p)
multPolyMAux x (Poly p) | length p == 0 = Cons 0
                        | otherwise = addPolyM multip2 ps
                        where 
                            ps = (Poly (Cons 0 : elems (multPolyMAux x (Poly (tail p)))))
                            multip2 = Poly [multPolyM x (head p)]



multPolyMRec :: [MulPoly] -> [MulPoly] -> [MulPoly]
multPolyMRec [] p2 = [Cons 0]
multPolyMRec (x:xs) p2 = (multPolyMAux x (Poly p2)) : (multPolyMRec xs (Cons 0 : p2))

-- REMOVE NULL COEFFICIENTS
--

rmZeros :: MulPoly -> MulPoly
rmZeros (Cons a) = (Cons a)
rmZeros (Poly p) | zerosOnly p' = Cons 0
                 | otherwise = (Poly (rmLastZeros (reverse p')))
                    where
                        p' = map rmZeros p


rmLastZeros [] = []
rmLastZeros ((Cons x):xs) = if x == 0 then rmLastZeros xs else reverse ((Cons x):xs)
rmLastZeros ((Poly x):xs) = reverse ((Poly x):xs)


zerosOnly [] = True
zerosOnly ((Cons x):xs) = (x == 0) && zerosOnly xs
zerosOnly ((Poly x):xs) = False



-- AUXILIARY FUNCTIONS
--

-- Division by an integer
divPoly (Cons a) x = Cons (div a x)
divPoly (Poly p) x = Poly (map (\el -> divPoly el x) p)


-- Given a MulPoly, return an array of MulPoly
elems :: MulPoly -> [MulPoly]
elems (Cons a) = [Cons a]
elems (Poly p) = p

-- Project a polynomial into GF(m)
polyMod :: MulPoly -> Int -> MulPoly
polyMod (Cons a) m = Cons (rem a m)
polyMod (Poly p) m | length p == 0 = Poly p
                   | otherwise = Poly (map (\el -> polyMod el m) p)



-- Find the maximum degree in a variable
maxDegree :: MulPoly -> Int -> Int
maxDegree (Cons a) _ = 0
maxDegree (Poly p) v | v==1 = (length p)-1
                     | otherwise = maximum (map (\el -> maxDegree el (v-1)) p)
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
chunkList :: Int -> [a] -> [[a]]
chunkList _ [] = []
chunkList n xs = x1 : (chunkList n x2)
                where
                (x1,x2) = splitAt n xs


intgToIntList [] = []
intgToIntList (x:xs) = (fromIntegral x) : (intgToIntList xs)


newRandPoly :: Int -> Int -> [Int] -> [Int] -> MulPoly
newRandPoly _ _ [] _ = Cons 1
newRandPoly _ _ _ [] = Cons 1
newRandPoly v d xs ys | v <= 1 = Poly coefs
                      | otherwise = Poly [multPolyM c (nextPoly a b) | (c,(a,b)) <- cxyzip]
                      where
                        (x1,x2) = splitAt (d+1) xs
                        (y1,y2) = splitAt (d+1) ys
                        xy = zip x1 y1
                        coefs = [if (mod b 13 < 8) then (Cons a) else (Cons 0) | (a,b) <-  xy]
                        nextLen = (d+1)^(v-1)
                        nextPoly a b = newRandPoly (v-1) d a b
                        cxyzip = zip coefs (zip (chunkList nextLen x2) (chunkList nextLen y2))


randomList :: Int -> IO([Int])
randomList 0 = return []
randomList n = do
  r  <- randomRIO (-1000,1000)
  rs <- randomList (n-1)
  return (r:rs)


randPoly v d xs ys = rmZeros (polyMod (newRandPoly v d (intgToIntList xs) (intgToIntList ys)) 1000)



{-
rd1 = [1..1000000000]
rd2 = [2 | i<- rd1]
rdPoly = rmZeros (polyMod (newRandPoly 6 3 rd1 rd1) 1000)
-}


main :: IO ()
main =  do
       rd1 <- randomList 1000000
       rd2 <- randomList 1000000
       let rdpoly = (randPoly 7 4 rd1 rd2)
       print(rdpoly)
     --  g <- newStdGen
     --  h <- newStdGen
 --      let rdList = (take 1000000 (randomRs (-1000,1000) g)) :: [Random Int]
   --    let rdNum = take 1000000 (randomRs (0, 200) h)
   --    print(10)
--       print(rmZeros (polyMod (newRandPoly 10 10 (intgToIntList rdList) (intgToIntList rdNum)) 1000))
