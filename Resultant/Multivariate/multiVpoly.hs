data MulPoly = Cons Int | Poly [MulPoly] deriving (Show)

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



multPolyM :: MulPoly -> MulPoly -> MulPoly
multPolyM (Cons a) (Cons b) = Cons (a*b)
multPolyM (Cons a) (Poly p) | (length p == 0 || a == 0) = Cons 0
                            | otherwise = Poly (map (\el -> multPolyM (Cons a) el) p)
multPolyM (Poly p) (Cons a) = multPolyM (Cons a) (Poly p)
multPolyM (Poly p1) (Poly p2) | length p1 == 0 = Cons 0
                              | length p2 == 0 = Cons 0
                              | length p1 == 1 = addPolyM (multPolyM (head p1) (head p2)) (multPolyM (head p1) (Poly (Cons 0 : tail p2)))
                              | length p2 == 1 = addPolyM (multPolyM (head p1) (head p2)) (multPolyM (head p2) (Poly (Cons 0 : tail p1)))
                              | otherwise = addPolyList (multPolyMRec p1 p2)




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


addPolyList :: [MulPoly] -> MulPoly
addPolyList [] = Cons 0
addPolyList (x:xs) = addPolyM x (addPolyList xs)


elems :: MulPoly -> [MulPoly]
elems (Cons a) = [Cons a]
elems (Poly p) = p
