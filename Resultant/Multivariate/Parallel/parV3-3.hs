{- 
 <Parallel implementation of multivariate polynomial resultant thanks to an algorithm 
 using the Chineses remainder theorem, interpolation and evaluation homomorphism 
 to reduce the problem over GF(p). 
 Source: G.E. COLLINS, "The Calculation of Multivariate Polynomial Resultants", 1971.>
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



import Debug.Trace
import Control.Parallel
import Control.Parallel.Strategies
import Control.DeepSeq as DeepSeq
import System.Environment

data MulPoly = Cons Integer | Poly [MulPoly] deriving (Show,Read)

instance DeepSeq.NFData (MulPoly) where
  rnf (Cons c) = DeepSeq.rnf c
  rnf (Poly p) = DeepSeq.rnf p

-------------------------------------------------------
-------------------------------------------------------
---- OPERATIONS ON MULTIVARIATE POLYNOMIALS

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


-- Find the maximum norm of a polynomial
maxNorm (Poly p) = maximum (map polyNorm p)
maxNorm (Cons a) = abs a

polyNorm :: MulPoly -> Integer
polyNorm (Cons a) = abs a
polyNorm (Poly p) | length p == 0 = 0
                  | otherwise = polyNorm (head p) + polyNorm (Poly (tail p))


-- Project a polynomial into GF(m)
polyMod :: MulPoly -> Integer -> MulPoly
polyMod (Cons a) m = Cons (rem a m)
polyMod (Poly p) m | length p == 0 = Poly p
                   | otherwise = Poly (map (\el -> polyMod el m) p)


-- Find the maximum degree in a variable
maxDegree :: MulPoly -> Integer -> Integer
maxDegree (Cons a) _ = 0
maxDegree (Poly p) v | v==1 = toInteger(length p)-1
                     | otherwise = maximum (map (\el -> maxDegree el (v-1)) p)


-- Return (x_r - b)
monomial r b | r == 1 = Poly [Cons (-b), Cons 1]
             | otherwise = Poly[monomial (r-1) b]



-- Evaluate a polynomial in a variable
--
evalVariable :: MulPoly -> Integer -> Integer -> MulPoly
evalVariable (Cons a) _ _ = Cons a
evalVariable (Poly p) v x | v == 1 = Poly [evalRec p x 0]
                          | otherwise = Poly (map (\el -> evalVariable el (v-1) x) p)


evalRec :: [MulPoly] -> Integer -> Integer -> MulPoly 
evalRec [] _ _ = Cons 0
evalRec ((Cons a):ys) x i = addPolyM (Cons (a * x^i)) (evalRec ys x (i+1)) 
evalRec ((Poly p):ys) x i = addPolyM (multPolyM (Cons (x^i)) (Poly p)) (evalRec ys x (i+1))




-- Try to transform into a univariate polynomial
--
multiToUniV :: MulPoly -> [Rational]
multiToUniV (Cons a) = [toRational a]
multiToUniV (Poly p) = if b then l else [] where (b, l) = isUnivariate p


onlyCons :: [MulPoly] -> (Bool,[Rational])
onlyCons [] = (True,[])
onlyCons ((Cons a):xs) = (b, l ++ [toRational a]) where (b,l) = onlyCons xs
onlyCons ((Poly p):xs) = ((length p == 1) && pb && b, l ++ pl)
                        where 
                            (b,l) = onlyCons xs
                            (pb, pl) = onlyCons p


isUnivariate :: [MulPoly] -> (Bool,[Rational])
isUnivariate [] = (True,[])
isUnivariate ((Cons a):xs) = (b, l ++ [toRational a])  where  (b, l) = onlyCons xs
isUnivariate ((Poly p):xs) | length xs == 0 = isUnivariate p
                           | otherwise = onlyCons ((Poly p):xs)



-------------------------------------------------------
-------------------------------------------------------
---- CPRES ALGORITHM


-- INTERPOLATION
-- Give the unique polynomial G such that:
-- G(x_1,...,x_(r-1),b_i) = A(x_1,...,x_(r-1),b_i) for b_i in D(x_r)
-- G(x_1,...,x_(r-1),b) = C(x_1,...,x_(r-1))
--
interpolate polyD b polyA polyC p r = addPoly (divPoly (multPoly (addPoly polyC polyA' p) polyD p) evalDb) polyA p
                                    where 
                                    polyA' = multPolyM (Cons (-1)) (evalVariable polyA r b)
                                    evalDb = round ((multiToUniV (evalVariable polyD r b))!!0)



-- CPRES
-- Given A and B being polynomials over GF(p) with positive degrees in x_r,
-- return C(x_1,...,x_(r-1)) the resultant of A and B over GF(p) with respect to x_r
--
algoCPRES polyA polyB p r | (toInteger(length univA) == mr+1) && (toInteger(length univB) == nr+1) = (Cons (round (resultant univA univB)), True)
                          | otherwise = algoCpresRec polyA polyB (Cons 0) (Cons 1) 0 p k r
                          where
                            mr = maxDegree polyA 1
                            nr = maxDegree polyB 1
                            mr_1 = maxDegree polyA r
                            nr_1 = maxDegree polyB r
                            k = mr*nr_1 + nr*mr_1 + 1
                            univA = multiToUniV polyA
                            univB = multiToUniV polyB


algoCpresRec polyA polyB polyC polyD b p k r | b==p = traceShow "b=p" (polyC, False)
                                             | (maxDegree polyA 1 > maxDegree polyA' 1) || (maxDegree polyB 1 > maxDegree polyB' 1) = algoCpresRec polyA polyB polyC polyD (b+1) p k r
                                             | (maxDegree polyD' r) <= k = algoCpresRec polyA polyB polyG polyD' (b+1) p k r
                                             | otherwise = (polyG, True)
                                             where
                                                polyA' = rmZeros (polyMod (evalVariable polyA r b) p)
                                                polyB' = rmZeros (polyMod (evalVariable polyB r b) p)
                                                polyC' = fst (algoCPRES polyA' polyB' p (r+1))
                                                polyG = interpolate polyD b polyC polyC' p r
                                                polyD' = multPoly (monomial r b) polyD p



-------------------------------------------------------
-------------------------------------------------------
---- PRES ALGORITHM


-- Garner's algorithm to compute the Chinese remainder
-- Return C such that C mod Q = B and C mod p = A
--
chineseRem :: Integer -> Integer -> Integer -> Integer -> Integer
chineseRem q p b a  = d'*q + b 
                    where
                        b' = if 2*(abs b) > q then traceShow ("B > Q/2") (mod b p) else mod b p
                        q' = mod q p
                        d = mod (div (a-b') q') p
                        d' = if (2*d > p) then d - p else d



-- Apply the chinese remainder to pairs of corresponding coefficients of two polynomials
--
polyChineseRem :: MulPoly -> MulPoly -> Integer -> Integer -> MulPoly
polyChineseRem (Cons a) (Cons b) q p = (Cons (chineseRem q p b a))
polyChineseRem (Poly []) b q p = b
polyChineseRem a (Poly []) q p = a
polyChineseRem (Cons a) (Poly pb) q p = Poly ((polyChineseRem (Cons a) (head pb) q p) : (tail pb))
polyChineseRem (Poly pa) (Cons b) q p = Poly ((polyChineseRem (head pa) (Cons b) q p) : (tail pa))
polyChineseRem (Poly (x:xs)) (Poly (y:ys)) q p = Poly ((polyChineseRem x y q p) : (elems (polyChineseRem (Poly xs) (Poly ys) q p)))



-- PRES
-- Given A(x_1,...,x_r) and B(x_1,...,x_r), return their resultant C(x_1,...,x_(r-1)) with respect to x_r.
--
algoPRES polyA polyB primeList = algoPresRec (rmZeros polyA) (rmZeros polyB) (Cons 0) primeList 1 f 
                                where
                                    m = maxDegree polyA 1
                                    n = maxDegree polyB 1
                                    d = maxNorm polyA
                                    e = maxNorm polyB
                                    f = 2*(product [1..(m+n)])*d^n*e^m



algoPresRec polyA polyB polyC (p:primes) q f    | length primes == 0 = traceShow ("no more primes") polyD
                                                | (maxDegree polyA 1 > maxDegree polyA' 1) || (maxDegree polyB 1 > maxDegree polyB' 1) || (cpres == False) || (2*(maxNorm polyC) > q) = 
                                                    algoPresRec polyA polyB polyC primes q' f
                                                | otherwise = if (q > f) then polyD else algoPresRec polyA polyB polyD primes q' f
                                                where
                                                    polyA' = rmZeros (polyMod polyA p)
                                                    polyB' = rmZeros (polyMod polyB p)
                                                    (polyC', cpres) = algoCPRES polyA' polyB' p 2
                                                    polyD = polyChineseRem polyC' polyC q p
                                                    q' = p*q
                                                    

-- PARALLEL
--

algoPRESPar polyA polyB primeList = applyChineseRemList (Cons 0) polyList
                                     where
                                        m = maxDegree polyA 1
                                        n = maxDegree polyB 1
                                        d = maxNorm polyA
                                        e = maxNorm polyB
                                        f = 2*(product [1..(m+n)])*d^n*e^m
                                        qpList = listQP 1 primeList f
                                        polyList = parMap (rpar `dot` rdeepseq) (\el -> algoPresParRec polyA polyB el) qpList




algoPresParRec polyA polyB (q,p) = (bool, polyC', p, q)
                              where
                                polyA' = rmZeros (polyMod polyA p)
                                polyB' = rmZeros (polyMod polyB p)
                                (polyC', cpres) = algoCPRES polyA' polyB' p 2 -- `using` strat
                                bool = (maxDegree polyA 1 == maxDegree polyA' 1) && (maxDegree polyB 1 == maxDegree polyB' 1) && cpres
             


listQP :: Integer -> [Integer] -> Integer -> [(Integer,Integer)]
listQP q [] f = []
listQP q (x:xs) f | q<=f = (q,x) : (listQP (q*x) xs f)
                  | otherwise = if (q==1) then (q,x) : (listQP (q*x) xs f) else [(q,x)]


applyChineseRemList polyC [] = polyC
applyChineseRemList polyC ((bool, polyC', p, q):xs) | (bool == True && (2*(maxNorm polyC)<q)) = applyChineseRemList (polyChineseRem polyC' polyC q p) xs
                                                    | otherwise = applyChineseRemList polyC xs



---------------------------------------------------------------------------------------------------------
-- PRIMES GENERATION
-- Source: http://wiki.haskell.org/Prime_numbers
----------------------------------------------------------------------------------------------------------


union (x:xs) (y:ys) = case (compare x y) of 
           LT -> x : union  xs  (y:ys)
           EQ -> x : union  xs     ys 
           GT -> y : union (x:xs)  ys
union  xs     []    = xs
union  []     ys    = ys


_Y g = g (_Y g) 

joinT ((x:xs):t) = x : union xs (joinT (pairs t))    -- set union, ~=
  where  pairs (xs:ys:t) = union xs ys : pairs t     --    nub.sort.concat

primesTMWE = [1,3,5,7] ++ _Y ((11:) . tail  . gapsW 11 wheel 
                                    . joinT . hitsW 11 wheel)
    
gapsW k (d:w) s@(c:cs) | k < c     = k : gapsW (k+d) w s    -- set difference
                       | otherwise =     gapsW (k+d) w cs   --   k==c
hitsW k (d:w) s@(p:ps) | k < p     =     hitsW (k+d) w s    -- intersection
                       | otherwise = scanl (\c d->c+p*d) (p*p) (d:w) 
                                       : hitsW (k+d) w ps   --   k==p 

wheel = 2:4:2:4:6:2:6:4:2:4:6:6:2:6:4:2:6:4:6:8:4:2:4:2:
        4:8:6:4:6:2:4:6:2:6:6:4:2:4:6:2:6:4:2:4:2:10:2:10:wheel


primesFromTMWE primes m = dropWhile (< m) [2,3,5,7,11] 
                          ++ gapsW a wh2 (compositesFrom a)
    where
    (a,wh2) = rollFrom (snapUp (max 3 m) 3 2)
    (h,p2:t) = span (< z) $ drop 4 primes           -- p < z => p*p<=a
    z = ceiling $ sqrt $ fromIntegral a + 1         -- p2>=z => p2*p2>a
    compositesFrom a = joinT (joinST [multsOf p  a    | p <- h ++ [p2]]
                                   : [multsOf p (p*p) | p <- t] )


joinST (xs:t) = (union xs . joinST . pairs) t
    where
    pairs (xs:ys:t) = union xs ys : pairs t
    pairs t         = t
joinST []     = []


snapUp v o step = v + (mod (o-v) step)              -- full steps from o
multsOf p from = scanl (\c d->c+p*d) (p*x) wh       -- map (p*) $
    where                                           --   scanl (+) x wh
    (x,wh) = rollFrom (snapUp from p (2*p) `div` p) --   , if p < from 

wheelNums  = scanl (+) 0 wheel
rollFrom n = go wheelNums wheel 
    where 
    m = (n-11) `mod` 210  
    go (x:xs) ws@(w:ws2) | x < m = go xs ws2
                         | True  = (n+x-m, ws)      -- (x >= m)



---------------------------------------------------------------------------------------------------------
-- UNIVARIATE RESULTANT
----------------------------------------------------------------------------------------------------------

-- This algorithm is based on the pseudo-code from Antonio Machi 
-- in "Algebra for Symbolic Computation"
--
resultant :: [Rational] -> [Rational] -> Rational
resultant p1 p2 | n > m = (-1)^(m*n) * resultant p2 p1
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
remainder :: [Rational] -> [Rational] -> [Rational]
remainder p1 p2 | (length p1) >= (length p2) = fst (euclideRec p1 p2 [])
                | otherwise = fst (euclideRec p2 p1 [])


-- Euclidean division algorithm based on the pseudo-code from Antonio Machi
--
euclideRec :: [Rational] -> [Rational] -> [Rational] -> ([Rational],[Rational])
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
addp :: [Rational] -> [Rational] -> [Rational]
addp p1 p2 | (length p1) >= (length p2) = polyAddrec (reverse p1) (reverse p2) []
           | otherwise = polyAddrec (reverse p2) (reverse p1) []


polyAddrec :: [Rational] -> [Rational] -> [Rational] -> [Rational]
polyAddrec p1 [] res = rmEmptyCoef (reverse (res ++ p1))
polyAddrec (x:xs) (y:ys) res = polyAddrec xs ys (res ++ [z])
                               where z = x + y



-- Multiplication
--
multp :: [Rational] -> [Rational] -> [Rational]
multp p1 p2 = polyMult (reverse p1) p2


polyMult :: [Rational] -> [Rational] -> [Rational]
polyMult [] _ = []
polyMult _ [] = []
polyMult (x:xs) ys = addp (map (*x) ys) ((polyMult (xs) ys) ++ [0])



-------------------------------------------------------
-------------------------------------------------------
---- AUXILIARY FUNCTIONS


-- Remove the coefficients of highest degree which are null
-- so that calculating the degree thanks to the length remains consistent
--
rmEmptyCoef :: [Rational] -> [Rational]
rmEmptyCoef [] = []
rmEmptyCoef (x:xs) | x == 0 = rmEmptyCoef xs
                   | otherwise = (x:xs)


-- Divide the leading monomials of two polynomials
-- The first polynomial must be of degree greater than the second
--
divMonom :: [Rational] -> [Rational] -> [Rational]
divMonom [] _ = []
divMonom _ [] = []
divMonom (x:xs) (y:ys) | (length xs) < (length ys) = []
                       | otherwise = (x/y) : [0 | i <- [1..((length xs) - (length ys))]]


polyEval :: [Rational] -> Integer -> Integer
polyEval [] b = 0
polyEval (x:xs) b = (round x)*b^(length xs) + polyEval xs b

----------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------


-- TEST
--
-- a = y^2 * z^2 + 3*z + 8*t + 12*t^2*x^2 - 2*x-z
polynomA = Poly [Poly [ Poly [Poly [Cons 0, Cons 8], Cons 3], Cons 0, Poly [Poly [Cons 0, Cons 0, Cons 2]]], Poly [ Poly [Cons 0, Cons (-2)]], Poly [ Poly [Poly [Cons 0, Cons 0, Cons 0, Cons 12]]]]

-- b = 5 + 2*z*x + y*x^2 + 10*x^3*y*z*t
polynomB = Poly [Cons 5, Poly [Poly [Cons 0, Cons 2]], Poly [Cons 0, Cons 1], Poly [Cons 0, Poly [Cons 0, Poly [Cons 0, Cons 10]]]]

polynomC = Poly [Poly [Poly [Cons 3, Cons 1], Cons 5], Cons 2]

polynomD = Poly [Poly [Cons 0, Cons 1], Cons 0, Cons 1] 


polynomA2 = (multPolyM polynomB polynomA)


polynomB2 = Poly [Poly [Poly [Poly [Cons 11]]],Poly [Poly [Cons (-2)]],Poly [Poly [Poly [Cons 12]]]]

polynomC2 = Poly [Poly [Poly [Poly [Cons 1, Cons 2, Cons 3, Cons 4]]]]

polynomE = Poly[Poly [Cons 0, Cons 1], Cons 1]

polynomF = Poly [Poly [Cons 0, Cons 0, Cons 0, Cons (-1)], Cons 0, Cons 0, Cons 1]

-- z^2 + y + x
polynomG = Poly [Poly [Poly[ Cons 0, Cons 0, Cons 1], Cons 1], Cons 1]

-- x^2*z*y
polynomH = Poly [Cons 0, Cons 0, Poly [Poly [ Cons 0, Cons 1], Cons 1]]

highPrimes :: [Integer]
highPrimes = take 100 (primesFromTMWE primesTMWE (10^5))

randPoly1 = Poly [Cons 0,Cons 0,Poly [Poly [Cons 0,Poly [Cons 0,Cons 48,Cons (-52)],Cons 0,Poly [Cons 52,Cons (-84),Cons 0,Cons (-80)]],Poly [Poly [Cons 35,Cons (-45),Cons 0,Cons (-50),Cons 10],Poly [Cons 0,Cons (-50),Cons 0,Cons 0],Poly [Cons (-10),Cons (-10),Cons 0,Cons (-50),Cons 90]],Poly [Cons 0,Poly [Cons 0,Cons 0,Cons 0,Cons 30,Cons (-5)],Poly [Cons 80,Cons 40,Cons (-60),Cons 0,Cons (-80)],Poly [Cons (-10),Cons 0,Cons 10]],Poly [Cons 0,Poly [Cons 5,Cons 35,Cons 0,Cons 45,Cons (-45)],Poly [Cons (-50)],Poly [Cons 0,Cons 0,Cons 0,Cons 66]],Poly [Poly [Cons 0,Cons (-20),Cons 0,Cons (-40),Cons (-60)],Poly [Cons 52,Cons (-16),Cons (-76),Cons 60],Poly [Cons 0,Cons (-64)]]],Poly [Cons 0,Poly [Cons 0,Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons 20,Cons 0]],Poly [Cons 0,Cons 0,Poly [Cons (-4),Cons 0,Cons 0,Cons 8]]],Poly [Cons 0,Poly [Poly [Cons (-62),Cons (-41),Cons (-29),Cons 52,Cons 14],Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons 0],Poly [Cons 0,Cons (-56),Cons 14,Cons 45],Poly [Cons 0,Cons 0,Cons 34,Cons (-27)]],Cons 0,Cons 0,Poly [Poly [Cons 0,Cons 0,Cons 0,Cons (-80),Cons 30],Poly [Cons 80,Cons (-10),Cons (-70),Cons 90]]]]



randPoly2 = Poly [Cons 0,Poly [Poly [Cons 0,Poly [Cons 0,Cons (-60),Cons (-72),Cons 0,Cons 84],Cons 0,Poly [Cons (-96),Cons 0,Cons 6,Cons 78]],Poly [Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons 0]],Poly [Cons 0,Poly [Cons (-86),Cons (-62),Cons (-10),Cons 54,Cons (-66)],Poly [Cons 0,Cons 0,Cons (-10),Cons 50,Cons 5],Poly [Cons 26,Cons 58,Cons 0,Cons (-72),Cons 87]]],Poly [Cons 0,Poly [Cons 0,Cons 0,Poly [Cons (-20),Cons 0,Cons 0,Cons (-20)],Poly [Cons 0,Cons (-88),Cons 0,Cons 20,Cons 96]],Poly [Poly [Cons 20,Cons (-20),Cons (-20),Cons 0,Cons 80],Poly [Cons (-80),Cons (-52),Cons 68,Cons 4,Cons 56],Cons 0,Poly [Cons 0,Cons 12,Cons (-44),Cons 12,Cons (-28)]],Poly [Poly [Cons 0,Cons 60,Cons 20,Cons (-20),Cons (-20)],Cons 0,Poly [Cons 80,Cons (-40)],Poly [Cons (-60),Cons 0,Cons (-20),Cons 0,Cons 80]],Poly [Poly [Cons (-40),Cons (-56),Cons 0,Cons (-32)],Poly [Cons (-48),Cons (-40),Cons 0,Cons (-48),Cons (-40)],Poly [Cons 56,Cons 0,Cons (-44)]]]]


randPoly3 = Poly [Poly [Poly [Poly [Cons 0,Cons 0,Cons (-20),Cons 0],Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons 10],Cons 0,Poly [Cons 80,Cons 80,Cons 0,Cons 40,Cons (-60)]],Cons 0,Cons 0,Poly [Poly [Cons 32,Cons 0,Cons 0,Cons 36,Cons 40],Poly [Cons 84,Cons (-68),Cons 76,Cons 0,Cons (-72)],Cons 0,Poly [Cons 0,Cons 80,Cons (-80),Cons (-60)]]],Poly [Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 96,Cons (-48),Cons 44,Cons (-28),Cons (-8)],Poly [Cons 88,Cons 44,Cons 0,Cons (-76)]],Cons 0,Poly [Cons 0,Poly [Cons 0,Cons 88,Cons (-80),Cons (-82)],Cons 0,Poly [Cons (-72),Cons (-16),Cons (-96)]]],Cons 0,Poly [Poly [Poly [Cons 0,Cons 20,Cons 0,Cons 0,Cons 20]],Cons 0,Poly [Poly [Cons 0,Cons 0,Cons (-76),Cons (-10),Cons (-34)],Poly [Cons (-32),Cons 72,Cons 12,Cons (-28),Cons (-88)],Poly [Cons 28,Cons 52]],Poly [Poly [Cons (-42),Cons (-50),Cons (-74)],Cons 0,Poly [Cons 0,Cons (-20),Cons 28]],Poly [Poly [Cons 0,Cons 0,Cons 88,Cons 0,Cons 12],Poly [Cons (-20),Cons 84,Cons 96,Cons (-88)]]],Poly [Cons 0,Poly [Poly [Cons 0,Cons 98,Cons 0,Cons 72],Poly [Cons 0,Cons (-38),Cons 0,Cons 86,Cons 42],Poly [Cons 0,Cons 0,Cons 0,Cons (-60)],Poly [Cons (-64),Cons 40,Cons 0,Cons 0,Cons 20]],Poly [Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons 0],Cons 0,Cons 0,Poly [Cons 20,Cons 0,Cons (-60),Cons 20,Cons 0]],Poly [Poly [Cons (-20),Cons 0,Cons 0,Cons 0],Poly [Cons (-76),Cons 0,Cons 0,Cons 0,Cons 52],Poly [Cons 60,Cons (-28)],Poly [Cons 0,Cons (-60),Cons (-60)]]]]

randPoly4 = Poly [Cons 0,Cons 0,Poly [Cons 0,Poly [Poly [Cons 0,Cons 584,Cons (-64),Cons (-744),Cons 624,Cons 608,Cons (-416)],Cons 0,Cons 0,Cons 0,Poly [Cons 0,Cons 704,Cons 0,Cons 0,Cons (-88),Cons 0,Cons 592],Poly [Cons (-280),Cons 264,Cons 768,Cons 672,Cons 0,Cons 32,Cons 520]],Cons 0,Cons 0,Poly [Poly [Cons (-616),Cons 0,Cons 312,Cons (-968),Cons 824,Cons (-592),Cons 928],Poly [Cons 840,Cons 0,Cons (-640),Cons 80,Cons 760,Cons (-120),Cons 40],Cons 0,Cons 0,Poly [Cons 200,Cons (-400),Cons 0,Cons 0,Cons 0,Cons 800],Poly [Cons (-728),Cons 0,Cons 0,Cons 656,Cons 0,Cons 888,Cons 464]]],Poly [Poly [Poly [Cons (-400),Cons 400,Cons 400,Cons 0,Cons 200],Poly [Cons 388,Cons 588,Cons (-412),Cons 220,Cons 0,Cons 0,Cons 514],Poly [Cons 884,Cons 516,Cons 390,Cons (-574),Cons 0,Cons 136,Cons 732],Cons 0,Cons 0,Poly [Cons (-918),Cons (-882),Cons 0,Cons 0,Cons 0,Cons 236]],Poly [Poly [Cons 440,Cons (-22),Cons (-336),Cons (-716),Cons 0,Cons 0,Cons (-516)],Cons 0,Poly [Cons (-504),Cons 0,Cons (-552),Cons 0,Cons (-984),Cons (-568)],Poly [Cons 0,Cons (-28),Cons (-636),Cons 0,Cons (-212),Cons (-568),Cons (-940)],Cons 0,Poly [Cons (-330),Cons 708,Cons 2,Cons 0,Cons 0,Cons 356,Cons (-314)]],Poly [Poly [Cons 0,Cons (-200),Cons (-80),Cons (-840),Cons 0,Cons (-480)],Poly [Cons 0,Cons 0,Cons 472,Cons (-48),Cons 392,Cons 920],Poly [Cons 0,Cons 104,Cons 0,Cons 976,Cons 0,Cons 0,Cons 880],Poly [Cons (-504),Cons 0,Cons 0,Cons 0,Cons 176,Cons 440]],Poly [Cons 0,Poly [Cons 344,Cons 888,Cons 136,Cons (-832),Cons 0,Cons (-616),Cons (-960)],Cons 0,Cons 0,Poly [Cons 0,Cons 712,Cons (-456),Cons 856,Cons (-824)],Poly [Cons (-556),Cons 0,Cons 0,Cons 356,Cons 0,Cons (-616),Cons (-224)]],Cons 0,Poly [Poly [Cons (-360),Cons (-850),Cons (-990),Cons (-290),Cons (-830)],Cons 0,Poly [Cons 712,Cons 0,Cons 988,Cons 0,Cons 0,Cons (-958),Cons (-298)],Cons 0,Cons 0,Poly [Cons (-672),Cons 504,Cons (-608),Cons 480,Cons (-952),Cons (-536),Cons (-672)]],Poly [Cons 0,Cons 0,Poly [Cons 820,Cons 0,Cons (-384),Cons 164,Cons (-12)],Poly [Cons 849,Cons 0,Cons (-888),Cons (-589),Cons 0,Cons (-603),Cons 97],Poly [Cons 0,Cons 112,Cons 0,Cons (-712),Cons 88]]],Poly [Poly [Poly [Cons 0,Cons (-248),Cons (-144),Cons 304]],Poly [Cons 0,Poly [Cons 0,Cons (-688),Cons 752,Cons 0,Cons 0,Cons 0,Cons 528],Cons 0,Cons 0,Poly [Cons (-560),Cons 0,Cons (-632),Cons 624,Cons 0,Cons 192,Cons 88],Poly [Cons 560,Cons 800,Cons (-760),Cons (-480),Cons 600,Cons 720,Cons (-640)]],Poly [Cons 0,Poly [Cons 408,Cons 0,Cons 0,Cons (-40),Cons 0,Cons 760,Cons (-304)],Poly [Cons 0,Cons 0,Cons 760,Cons (-560),Cons (-280),Cons (-680),Cons (-480)],Poly [Cons (-968),Cons 0,Cons 0,Cons (-704),Cons (-664),Cons (-504),Cons 528]],Cons 0,Poly [Poly [Cons 0,Cons (-8),Cons 744,Cons 0,Cons 0,Cons (-952),Cons (-336)],Cons 0,Poly [Cons (-280),Cons 0,Cons 0,Cons 208,Cons 0,Cons 0,Cons (-480)],Cons 0,Poly [Cons (-984),Cons 0,Cons 16,Cons (-896),Cons (-696),Cons (-600),Cons 152]],Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 120,Cons 0,Cons 232,Cons 984,Cons 0,Cons 808],Poly [Cons 0,Cons (-200),Cons 0,Cons 680,Cons 760,Cons 400,Cons 400],Poly [Cons 0,Cons 200,Cons (-200),Cons 0,Cons 0,Cons 400]]],Cons 0,Poly [Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons (-760),Cons (-240),Cons (-480),Cons (-360)],Poly [Cons 840,Cons 0,Cons 0,Cons (-640),Cons 0,Cons (-880)]],Cons 0,Poly [Cons 0,Poly [Cons 0,Cons 0,Cons (-872),Cons 0,Cons 0,Cons 0,Cons 904],Poly [Cons 0,Cons (-8),Cons 456,Cons 0,Cons 192,Cons 32],Poly [Cons (-256),Cons (-160),Cons 784,Cons (-520),Cons (-808)],Poly [Cons 640,Cons 40,Cons 0,Cons 0,Cons (-880),Cons (-680)],Poly [Cons 784,Cons 0,Cons 0,Cons (-936),Cons (-600)]],Poly [Poly [Cons 136,Cons 88,Cons 0,Cons 280,Cons (-280),Cons (-16),Cons 624],Poly [Cons 560,Cons 712,Cons (-328),Cons 0,Cons (-536),Cons 0,Cons 992],Cons 0,Cons 0,Poly [Cons 0,Cons 872,Cons 304,Cons 88]]]]

randPoly5 = Poly [Poly [Poly [Poly [Cons 0,Cons 0,Cons 848,Cons 208,Cons 116,Cons (-452)]],Poly [Poly [Cons 0,Cons 0,Cons (-500),Cons 800],Poly [Cons 0,Cons 0,Cons 0,Cons (-600)],Cons 0,Poly [Cons 0,Cons (-200),Cons 400,Cons 700]],Poly [Poly [Cons (-80),Cons 0,Cons 0,Cons 20,Cons 560,Cons 640],Cons 0,Poly [Cons (-648),Cons (-16),Cons 728,Cons (-536),Cons (-328),Cons 120]],Poly [Cons 0,Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons 640,Cons 560,Cons (-680),Cons 320]],Poly [Poly [Cons 480,Cons 0,Cons 720,Cons (-720),Cons 800,Cons 200],Cons 0,Cons 0,Cons 0,Poly [Cons 656,Cons 840,Cons 0,Cons 0,Cons 0,Cons (-616)]]],Cons 0,Poly [Poly [Cons 0,Cons 0,Poly [Cons 0,Cons (-312),Cons (-104),Cons 360,Cons 0,Cons 40]],Poly [Poly [Cons 35,Cons (-761),Cons (-904),Cons 777,Cons 0,Cons (-952)],Poly [Cons 0,Cons 802,Cons (-95),Cons (-377)],Cons 0,Poly [Cons 34,Cons 0,Cons 793,Cons 0,Cons 839,Cons (-250)],Poly [Cons 72,Cons 0,Cons 0,Cons 0,Cons 528]]],Cons 0,Cons 0,Poly [Poly [Poly [Cons 8,Cons 0,Cons 0,Cons 0,Cons 0,Cons 912],Poly [Cons 0,Cons (-760),Cons 0,Cons (-264),Cons (-504),Cons (-656)],Poly [Cons 0,Cons 496,Cons 664,Cons 736,Cons (-136)],Cons 0,Poly [Cons 0,Cons 400,Cons 160,Cons 120,Cons (-424)]],Cons 0,Cons 0,Poly [Poly [Cons 464,Cons 0,Cons 0,Cons (-96),Cons 952,Cons 936],Poly [Cons (-824),Cons (-12),Cons 0,Cons (-408),Cons (-532)],Cons 0,Cons 0,Poly [Cons 220,Cons 0,Cons 64,Cons 716]],Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 320,Cons 0,Cons 120,Cons (-360)],Poly [Cons 0,Cons (-600),Cons 0,Cons 400,Cons (-800)]]]] 

randPoly6 = Poly []

randPoly7 = Poly [Poly [Cons 0,Cons 0,Poly [Poly [Cons 690,Cons (-928),Cons (-6),Cons 658,Cons 0,Cons 908],Poly [Cons (-266),Cons 0,Cons 0,Cons 0,Cons 884,Cons 0,Cons 958],Cons 0,Poly [Cons 0,Cons 856,Cons 0,Cons (-568),Cons 0,Cons 280],Poly [Cons (-266),Cons 0,Cons 0,Cons (-466),Cons 0,Cons 36,Cons (-268)]],Poly [Cons 0,Poly [Cons 0,Cons (-680),Cons (-10),Cons 0,Cons 0,Cons (-80),Cons 385],Poly [Cons 776,Cons 464,Cons 80,Cons (-240),Cons 440,Cons 0,Cons 704],Poly [Cons 770,Cons 0,Cons (-213),Cons 0,Cons (-328),Cons (-258)]],Cons 0,Poly [Poly [Cons 0,Cons (-440),Cons 0,Cons 0,Cons 0,Cons 0,Cons 642],Poly [Cons 0,Cons 0,Cons 0,Cons (-475),Cons (-625)],Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons 0,Cons 400,Cons (-896),Cons 72,Cons 464]],Poly [Poly [Cons 0,Cons 0,Cons 240,Cons 0,Cons 0,Cons 0,Cons 40],Poly [Cons (-80),Cons 560,Cons 0,Cons (-560),Cons 0,Cons 240,Cons 800],Poly [Cons 700,Cons 0,Cons 0,Cons (-60),Cons 980,Cons 0,Cons 440],Poly [Cons 0,Cons 0,Cons 440,Cons 800,Cons 0,Cons 0,Cons (-360)]]],Poly [Poly [Poly [Cons 570,Cons 120,Cons 0,Cons 0,Cons 0,Cons 150],Poly [Cons 0,Cons 128,Cons 660,Cons 0,Cons 127,Cons 0,Cons 816],Poly [Cons 0,Cons 0,Cons 0,Cons (-135),Cons (-160),Cons (-440),Cons 425],Poly [Cons 0,Cons 698,Cons 0,Cons 0,Cons 560,Cons 0,Cons (-292)],Poly [Cons (-267),Cons 0,Cons (-941),Cons 0,Cons 0,Cons 968,Cons (-580)],Poly [Cons 913,Cons 125,Cons 720,Cons (-468),Cons 503,Cons (-592),Cons 862]],Poly [Cons 0,Poly [Cons (-820),Cons 0,Cons (-100),Cons 880,Cons (-760),Cons (-500),Cons (-760)],Poly [Cons (-172),Cons 488,Cons 0,Cons 378,Cons 425,Cons 0,Cons 982],Poly [Cons 0,Cons (-124),Cons 870,Cons (-348),Cons (-774),Cons (-190)],Poly [Cons (-730),Cons 0,Cons 120],Poly [Cons 814,Cons 0,Cons 0,Cons (-26),Cons (-718),Cons (-729)]],Poly [Poly [Cons 0,Cons 0,Cons 448,Cons (-724),Cons 987,Cons (-675),Cons (-803)],Cons 0,Cons 0,Poly [Cons (-250),Cons 125,Cons 375,Cons 0,Cons 375,Cons 0,Cons (-750)]],Poly [Poly [Cons (-394),Cons 0,Cons 463,Cons 0,Cons 856],Poly [Cons 0,Cons 0,Cons (-400),Cons 500,Cons 0,Cons 780]],Poly [Cons 0,Poly [Cons 0,Cons 0,Cons (-284),Cons (-72),Cons 0,Cons (-460),Cons 592],Cons 0,Cons 0,Cons 0,Poly [Cons 512,Cons (-40),Cons (-88),Cons (-16),Cons 56,Cons 0,Cons (-536)]],Poly [Cons 0,Poly [Cons (-480),Cons (-960),Cons 0,Cons (-840),Cons 0,Cons 560],Cons 0,Poly [Cons 0,Cons (-80),Cons (-360),Cons 0,Cons 0,Cons 760],Poly [Cons 760,Cons 640,Cons 0,Cons 0,Cons (-440),Cons (-680),Cons (-360)]],Poly [Poly [Cons (-520)],Cons 0,Poly [Cons 568,Cons (-720),Cons 0,Cons 0,Cons 0,Cons 232,Cons (-448)],Poly [Cons 0,Cons 0,Cons (-912),Cons 184,Cons (-932),Cons 0,Cons (-420)]]],Poly [Cons 0,Poly [Poly [Cons 0,Cons (-564),Cons (-260),Cons 796],Cons 0,Cons 0,Cons 0,Cons 0,Poly [Cons 0,Cons (-280),Cons 0,Cons 0,Cons (-208),Cons 8]],Cons 0,Cons 0,Poly [Poly [Cons 0,Cons 0,Cons (-700),Cons 0,Cons (-250)],Poly [Cons (-224),Cons 0,Cons 388,Cons 576,Cons 752,Cons 492,Cons 344],Poly [Cons 456,Cons 440,Cons (-920),Cons 0,Cons 72,Cons (-48),Cons (-560)],Poly [Cons (-104),Cons (-960),Cons (-988)],Cons 0,Poly [Cons 588,Cons (-606),Cons (-92),Cons (-648),Cons 0,Cons 596,Cons 32]],Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 0,Cons (-840),Cons (-240),Cons 0,Cons 0,Cons 648,Cons (-40)],Cons 0,Poly [Cons 800,Cons 0,Cons (-392),Cons (-280)]]],Cons 0,Poly [Poly [Poly [Cons 440,Cons 0,Cons 0,Cons 0,Cons (-680),Cons 0,Cons 680],Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons (-480),Cons 0,Cons 360,Cons 480],Poly [Cons 80,Cons 860,Cons (-340),Cons (-260),Cons (-120),Cons (-440)],Poly [Cons (-140),Cons 20,Cons 0,Cons (-580),Cons 0,Cons (-800),Cons 520]],Cons 0,Poly [Poly [Cons (-840),Cons 0,Cons (-440),Cons 680,Cons 0,Cons 340],Poly [Cons 0,Cons 940,Cons (-600),Cons 0,Cons (-680),Cons 0,Cons (-270)],Poly [Cons 220,Cons (-565),Cons 130,Cons 590,Cons (-70),Cons (-385),Cons 155],Poly [Cons 0,Cons 220,Cons (-360),Cons 0,Cons (-680)],Poly [Cons (-360),Cons 0,Cons 560,Cons (-600),Cons 920,Cons (-360)]],Cons 0,Poly [Poly [Cons (-744),Cons 0,Cons 0,Cons 0,Cons 0,Cons 696,Cons 868],Poly [Cons 872,Cons (-576),Cons 0,Cons (-80),Cons (-872),Cons 896,Cons 592],Poly [Cons 136,Cons (-132),Cons 644,Cons 0,Cons 764],Poly [Cons 0,Cons (-576),Cons 0,Cons 128,Cons 0,Cons 0,Cons 124],Poly [Cons (-300),Cons (-924),Cons 0,Cons 0,Cons 380,Cons 0,Cons 564]],Cons 0,Poly [Poly [Cons (-347),Cons (-518),Cons 0,Cons (-565)],Cons 0,Cons 0,Cons 0,Poly [Cons (-972),Cons 392,Cons (-180),Cons 0,Cons (-880),Cons 470,Cons 790]]],Cons 0,Poly [Poly [Poly [Cons (-672),Cons 0,Cons 104,Cons 0,Cons 0,Cons 112,Cons 344],Cons 0,Cons 0,Poly [Cons 0,Cons 608,Cons 792,Cons 0,Cons (-176),Cons 0,Cons (-880)]],Poly [Poly [Cons 268,Cons 348,Cons (-296),Cons 0,Cons (-824),Cons 632],Poly [Cons 264,Cons (-576),Cons (-496),Cons 0,Cons (-168),Cons 296,Cons (-672)],Cons 0,Poly [Cons 980,Cons 936,Cons 0,Cons (-404),Cons (-32),Cons (-92),Cons 80],Poly [Cons 80,Cons (-240),Cons 800,Cons (-240),Cons 0,Cons 160,Cons (-320)],Poly [Cons 272,Cons 0,Cons (-320),Cons 0,Cons 664]],Poly [Poly [Cons 510,Cons 0,Cons 0,Cons (-342),Cons 924,Cons (-682),Cons (-864)],Cons 0,Cons 0,Poly [Cons (-965),Cons (-854),Cons 828,Cons (-227),Cons 639,Cons 256],Cons 0,Poly [Cons 0,Cons 10,Cons 450,Cons (-260),Cons 420]],Poly [Cons 0,Cons 0,Poly [Cons 842,Cons 360,Cons (-88),Cons (-562),Cons 0,Cons 70],Poly [Cons (-182),Cons 0,Cons 0,Cons (-356),Cons (-590)],Poly [Cons (-636),Cons 544,Cons 0,Cons (-642),Cons 0,Cons 784,Cons (-772)],Poly [Cons 327,Cons 0,Cons 227]],Cons 0,Cons 0,Poly [Poly [Cons (-570),Cons (-70),Cons 450,Cons 0,Cons 0,Cons 510,Cons (-40)],Poly [Cons 0,Cons 160,Cons 70,Cons (-770),Cons (-10),Cons (-260),Cons 900],Cons 0,Poly [Cons 0,Cons (-20),Cons 620,Cons 0,Cons 0,Cons (-860)]]]]

randPoly8 = Poly [Poly [Cons 0,Cons 0,Poly [Cons 0,Cons 0,Poly [Cons 472,Cons 768,Cons 896,Cons (-924),Cons (-52),Cons (-364),Cons 648],Poly [Cons 0,Cons (-912),Cons 624,Cons (-820),Cons 0,Cons 360],Cons 0,Poly [Cons 956,Cons (-700),Cons (-508),Cons (-456),Cons (-996),Cons 0,Cons (-172)]],Poly [Cons 0,Cons 0,Cons 0,Poly [Cons 168,Cons 256,Cons 0,Cons (-544),Cons (-8),Cons 56],Cons 0,Poly [Cons 0,Cons (-136),Cons 0,Cons 0,Cons 296,Cons 344,Cons 8]],Poly [Poly [Cons (-728),Cons 0,Cons 400,Cons 0,Cons 0,Cons 456],Cons 0,Poly [Cons 0,Cons (-40),Cons 0,Cons 0,Cons 0,Cons 440],Cons 0,Poly [Cons (-688),Cons (-336),Cons (-632),Cons (-176),Cons (-312),Cons (-80)],Poly [Cons 0,Cons (-800),Cons 800,Cons 0,Cons 400,Cons 600]],Poly [Poly [Cons (-640),Cons (-800),Cons (-880),Cons 0,Cons (-680),Cons (-720)],Cons 0,Cons 0,Poly [Cons 450,Cons 300,Cons 0,Cons (-150)],Poly [Cons 0,Cons 0,Cons (-44),Cons 756,Cons (-2)]],Poly [Poly [Cons (-32),Cons (-640),Cons 0,Cons 56,Cons 0,Cons 336,Cons 664],Poly [Cons (-504),Cons (-944),Cons (-224),Cons 0,Cons 0,Cons (-504)],Poly [Cons 952,Cons 680,Cons (-344),Cons (-848),Cons 0,Cons 0,Cons (-392)],Poly [Cons (-960),Cons 60,Cons 240,Cons 0,Cons 160]]],Cons 0,Poly [Cons 0,Poly [Cons 0,Cons 0,Poly [Cons (-900),Cons 0,Cons (-487),Cons 537,Cons 0,Cons 0,Cons 534],Cons 0,Cons 0,Poly [Cons 0,Cons (-945),Cons (-555),Cons (-290),Cons 495,Cons (-445)]],Poly [Cons 0,Cons 0,Poly [Cons 0,Cons 96,Cons (-538),Cons 0,Cons (-194),Cons (-834)],Poly [Cons 0,Cons 572,Cons 0,Cons (-702),Cons 719,Cons 163],Cons 0,Poly [Cons 0,Cons (-982),Cons 932,Cons 0,Cons 0,Cons 0,Cons 272]],Poly [Cons 0,Poly [Cons 0,Cons 0,Cons 286,Cons 0,Cons 0,Cons (-602)],Poly [Cons 0,Cons (-90),Cons (-600),Cons (-190),Cons (-120)],Cons 0,Poly [Cons 0,Cons 432,Cons (-933),Cons (-146),Cons (-844),Cons 421,Cons 21]],Poly [Poly [Cons 200,Cons 0,Cons 0,Cons (-200),Cons 800,Cons 200,Cons (-800)],Poly [Cons 516,Cons 80,Cons 0,Cons 0,Cons (-668),Cons 764],Cons 0,Poly [Cons 0,Cons (-140),Cons 0,Cons 780,Cons 0,Cons 0,Cons 660],Poly [Cons 312,Cons 0,Cons 56,Cons 0,Cons (-96),Cons 240],Poly [Cons 660,Cons 0,Cons 340,Cons 0,Cons (-940),Cons (-340)]],Poly [Poly [Cons (-374),Cons (-8),Cons 254],Poly [Cons (-152),Cons 0,Cons (-648),Cons 0,Cons (-480),Cons 360],Poly [Cons 780,Cons (-864),Cons 0,Cons 618,Cons (-596),Cons 342],Poly [Cons 840,Cons 0,Cons (-360),Cons 600,Cons 40,Cons 240,Cons (-600)],Cons 0,Poly [Cons 0,Cons 0,Cons 324,Cons 0,Cons 0,Cons 0,Cons (-168)]],Poly [Poly [Cons (-960),Cons 0,Cons 520,Cons 400,Cons 0,Cons (-880)],Cons 0,Poly [Cons 600,Cons 0,Cons 920,Cons 0,Cons 0,Cons (-200)]]],Poly [Poly [Poly [Cons 40,Cons (-904),Cons 0,Cons 0,Cons (-512),Cons (-248),Cons 448],Poly [Cons 48,Cons 0,Cons (-336),Cons 0,Cons 152,Cons 40],Poly [Cons 0,Cons (-848),Cons 0,Cons (-936),Cons (-24)],Poly [Cons 0,Cons 520,Cons (-940),Cons 760,Cons 0,Cons (-580)]],Poly [Cons 0,Poly [Cons 686,Cons (-666),Cons 0,Cons (-436),Cons (-168),Cons 354,Cons 214],Cons 0,Cons 0,Poly [Cons 300,Cons 100]],Poly [Poly [Cons 0,Cons 944,Cons (-704),Cons 0,Cons 688],Poly [Cons 0,Cons (-88),Cons 0,Cons (-736),Cons 864,Cons (-664),Cons 480],Cons 0,Poly [Cons 912,Cons (-560),Cons 0,Cons 0,Cons 0,Cons (-56),Cons (-928)],Poly [Cons 0,Cons 0,Cons 104,Cons (-472),Cons 528,Cons (-784),Cons 32]],Poly [Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons (-176),Cons 716],Cons 0,Cons 0,Poly [Cons (-440),Cons 72,Cons 88,Cons (-72),Cons (-344),Cons (-656)],Poly [Cons 0,Cons (-408),Cons 264,Cons (-528),Cons 664,Cons 760,Cons 952],Poly [Cons 0,Cons (-724),Cons (-480),Cons (-184),Cons 516,Cons 0,Cons 552]],Cons 0,Poly [Cons 0,Poly [Cons 602,Cons 102,Cons 480,Cons 0,Cons (-888),Cons 0,Cons (-820)],Cons 0,Poly [Cons (-72),Cons 0,Cons (-496),Cons 0,Cons 0,Cons 0,Cons (-528)],Cons 0,Poly [Cons 0,Cons (-456),Cons (-272),Cons 0,Cons (-512),Cons 792,Cons (-432)]]],Cons 0,Poly [Poly [Poly [Cons 78,Cons (-860),Cons 408,Cons 0,Cons 0,Cons 334,Cons (-444)],Poly [Cons 0,Cons 0,Cons 30,Cons (-812),Cons 0,Cons 304,Cons (-430)],Poly [Cons 880,Cons 0,Cons (-194),Cons 0,Cons 0,Cons 984,Cons (-244)],Cons 0,Cons 0,Poly [Cons 0,Cons (-928),Cons 0,Cons 176,Cons 592,Cons (-784)]],Poly [Poly [Cons 0,Cons 0,Cons 636,Cons (-412),Cons 436],Cons 0,Poly [Cons 736,Cons 0,Cons (-48),Cons 0,Cons 520,Cons 0,Cons 708],Cons 0,Poly [Cons 892,Cons (-32),Cons 0,Cons 0,Cons 0,Cons 0,Cons 548],Poly [Cons (-680),Cons 892,Cons 0,Cons 0,Cons (-528),Cons (-840)]],Poly [Poly [Cons 0,Cons 0,Cons (-432),Cons 0,Cons (-560),Cons (-416),Cons 416],Cons 0,Cons 0,Poly [Cons 0,Cons 0,Cons 0,Cons 600,Cons (-480),Cons 0,Cons 784],Cons 0,Poly [Cons 256,Cons 0,Cons (-376),Cons (-584)]],Cons 0,Poly [Cons 0,Poly [Cons (-608),Cons 0,Cons 0,Cons 0,Cons 784,Cons 0,Cons 248],Poly [Cons 0,Cons 0,Cons 160,Cons 0,Cons 0,Cons (-400),Cons 680],Cons 0,Poly [Cons 848,Cons 248,Cons 0,Cons 0,Cons 824,Cons 0,Cons 416]],Cons 0,Poly [Cons 0,Poly [Cons (-16),Cons 0,Cons 0,Cons (-384),Cons 0,Cons 64],Cons 0,Poly [Cons 0,Cons 0,Cons (-296),Cons 0,Cons 792,Cons 0,Cons (-896)],Poly [Cons 720,Cons 0,Cons 0,Cons 0,Cons 40,Cons 360]]],Poly [Poly [Poly [Cons (-950),Cons 0,Cons 0,Cons (-975),Cons (-875),Cons (-75),Cons 175],Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons (-500),Cons 0,Cons (-750)],Cons 0,Cons 0,Poly [Cons 100,Cons (-200),Cons 600,Cons (-300),Cons (-700),Cons (-100),Cons 500],Poly [Cons 0,Cons 0,Cons 0,Cons 0,Cons 900,Cons 325,Cons (-950)]],Poly [Poly [Cons (-830),Cons (-960),Cons 0,Cons 0,Cons 0,Cons 0,Cons 30],Poly [Cons 0,Cons 710,Cons 850,Cons 0,Cons 0,Cons 0,Cons (-455)],Poly [Cons (-240),Cons 760,Cons 160,Cons 0,Cons (-200),Cons 880],Poly [Cons 0,Cons (-240),Cons 40,Cons 795,Cons (-135),Cons 0,Cons (-480)],Cons 0,Poly [Cons 0,Cons (-685),Cons 0,Cons 635,Cons (-815),Cons 840,Cons (-320)]],Poly [Poly [Cons 0,Cons 640,Cons 640,Cons (-560),Cons 440,Cons 840],Poly [Cons 0,Cons 440,Cons 0,Cons 0,Cons 280,Cons 840,Cons 320],Poly [Cons 0,Cons 0,Cons 0,Cons (-500),Cons 250],Cons 0,Poly [Cons 760,Cons 0,Cons (-560),Cons 0,Cons 0,Cons (-620)]],Poly [Poly [Cons (-695),Cons (-795),Cons 250,Cons 0,Cons 555,Cons (-535),Cons 70],Cons 0,Poly [Cons 0,Cons (-975),Cons (-250),Cons 0,Cons 0,Cons (-775)],Poly [Cons (-950),Cons 0,Cons 350,Cons (-300),Cons 0,Cons (-650)],Poly [Cons (-495),Cons 0,Cons 0,Cons 0,Cons (-295)],Poly [Cons (-420),Cons 860,Cons 0,Cons 0,Cons 0,Cons (-800),Cons 700]],Poly [Poly [Cons (-300),Cons 0,Cons 110,Cons (-550),Cons (-850)],Poly [Cons (-190),Cons 0,Cons 450,Cons 0,Cons 0,Cons (-540),Cons (-840)],Poly [Cons 730,Cons 960,Cons 0,Cons (-90),Cons (-240),Cons 0,Cons (-860)],Poly [Cons 0,Cons (-320),Cons (-300),Cons (-960),Cons 20,Cons (-320),Cons 600],Cons 0,Poly [Cons (-570),Cons 0,Cons (-880),Cons 0,Cons (-750),Cons (-325),Cons (-980)]],Cons 0,Poly [Poly [Cons 0,Cons 0,Cons 460,Cons 300,Cons 260,Cons 0,Cons 80],Cons 0,Poly [Cons 0,Cons (-825),Cons (-230),Cons 0,Cons 0,Cons 110],Poly [Cons (-400),Cons 970,Cons 165,Cons (-565),Cons (-415),Cons (-145),Cons 880]]]]

randPolyList = [randPoly1, randPoly2, randPoly3, randPoly4, randPoly5, randPoly6, randPoly7, randPoly8]

main :: IO ()
main =  do
args <- getArgs
let poly1 = read (args!!0) :: Int
let poly2 = read (args!!1) :: Int
print(algoPRESPar (randPolyList!!(poly1-1)) (randPolyList!!(poly2-1)) highPrimes)
--print(algoPRESPar randPoly1 randPoly3 highPrimes) 
--print(5)
