%default total

douti : Type -> Type -> Type
douti p q = (p->q, q->p)

data N = O | S N
Show N where
  show O = "0"
  show (S n) = "S" ++ show n

(+) : N -> N -> N
O     + n = n
(S m) + n = S (m + n)

(*) : N -> N -> N
O     * n = O
(S m) * n = n + (m * n)

I : N
I = S O

addZero : (n : N) -> n + O = n
addZero O = Refl
addZero (S k) = rewrite addZero k in Refl

addSucc : (m, n : N) -> m + (S n) = S (m + n)
addSucc O n = Refl
addSucc (S m) n = rewrite addSucc m n in Refl

加法交換則 : (m, n : N) -> m + n = n + m
加法交換則 O n = rewrite addZero n in Refl
加法交換則 (S m) n =
  rewrite addSucc n m in
  rewrite 加法交換則 m n in
  Refl 

加法結合則 : (a, b, c : N) -> (a + b) + c = a + (b + c)
加法結合則 O b c = Refl
加法結合則 (S a) b c = rewrite 加法結合則 a b c in Refl

mulZero : (n : N) -> n * O = O
mulZero O = Refl
mulZero (S n) = rewrite mulZero n in Refl

oneMul : (n : N) -> I * n = n
oneMul O = Refl
oneMul (S n) = rewrite oneMul n in Refl

mulOne : (n : N) -> n * I = n
mulOne O = Refl
mulOne (S n) = rewrite mulOne n in Refl

mulSucc : (m, n : N) -> m * (S n) = m + (m * n)
mulSucc O n = Refl
mulSucc (S m) n =
  rewrite mulSucc m n in 
  rewrite sym $ 加法結合則 m n (m * n) in
  rewrite sym $ 加法結合則 n m (m * n) in
  rewrite 加法交換則 n m in
  Refl

乗法交換則 : (m, n : N) -> m * n = n * m
乗法交換則 O n = rewrite mulZero n in Refl
乗法交換則 (S m) n = 
  rewrite mulSucc n m in
  rewrite 乗法交換則 m n in
  Refl

分配則 : (a, b, c : N) -> (a+b) * c = a*c + b*c
分配則 O b c = Refl
分配則 (S a) b c =
  rewrite 分配則 a b c in
  rewrite 加法結合則 c (a*c) (b*c) in 
  Refl
分配則' : (a : N) -> (b : N) -> (c : N) -> a * (b+c) = a*b + a*c
分配則' a b c =
  rewrite 乗法交換則 a (b+c) in
  rewrite 分配則 b c a in
  rewrite 乗法交換則 b a in
  rewrite 乗法交換則 c a in
  Refl

乗法結合則 : (a, b, c : N) -> (a * b) * c = a * (b * c)
乗法結合則 O b c = Refl
乗法結合則 (S a) b c = 
  rewrite 分配則 b (a*b) c in
  rewrite 乗法結合則 a b c in
  Refl

pow : N -> N -> N
pow m O     = I
pow m (S n) = m * (pow m n)

powOne : (n : N) -> pow n I = n
powOne n = rewrite mulOne n in Refl

onePow : (n : N) -> pow I n = I
onePow O = Refl
onePow (S n) = rewrite onePow n in Refl

指数法則1 : (a, m, n : N) -> (pow a m) * (pow a n) = pow a (m+n)
指数法則1 a O n = rewrite addZero (pow a n) in Refl
指数法則1 a (S m) n =
  rewrite sym $ 指数法則1 a m n in
  rewrite 乗法結合則 a (pow a m) (pow a n) in
  Refl

指数法則2 : (a, m, n : N) -> pow (pow a m) n = pow a (m*n)
指数法則2 a O n = rewrite onePow n in Refl
指数法則2 a m O = rewrite mulZero m in Refl
指数法則2 a m (S n) =
  rewrite mulSucc m n in
  rewrite sym $ 指数法則1 a m (m*n) in
  rewrite 指数法則2 a m n in
  Refl

指数法則3 : (a, b, n : N) -> pow (a*b) n = (pow a n) * (pow b n)
指数法則3 a b O = Refl
指数法則3 a b (S n) =
  rewrite 指数法則3 a b n in
  rewrite 乗法結合則 a (pow a n) (b * pow b n) in
  rewrite 乗法結合則 a b (pow a n * pow b n) in
  rewrite sym $ 乗法結合則 (pow a n) b (pow b n) in
  rewrite sym $ 乗法結合則 b (pow a n) (pow b n) in
  rewrite 乗法交換則 b (pow a n) in
  Refl

data (<=) : (m, n : N) -> Type where
  LteZero : O <= n 
  LteSucc : m <= n -> S m <= S n

data (<) : (m, n : N) -> Type where
  LtZero : O < S n
  LtSucc : m < n -> S m < S n

data (>=) : (m, n : N) -> Type where
  GteZero : m >= O 
  GteSucc : m >= n -> S m >= S n

data (>) : (m, n : N) -> Type where
  GtZero : S m > O
  GtSucc : m > n -> S m > S n

lteImplyPlusD : { m, n : N } -> m <= n -> (d : N ** m+d=n)
lteImplyPlusD {m=O}{n=d} LteZero = (d ** Refl)
lteImplyPlusD {m=S a}{n=S b} (LteSucc x) with (lteImplyPlusD x)
  | MkDPair d f = MkDPair d (rewrite f in Refl)

ltImplyLte : m < n -> m <= n
ltImplyLte LtZero = LteZero
ltImplyLte (LtSucc x) = LteSucc $ ltImplyLte x

flipLteGte : { m, n : N } -> (m <= n) -> (n >= m)
flipLteGte LteZero = GteZero
flipLteGte (LteSucc x) = GteSucc $ flipLteGte x

--nonZeroNotLessThanEqualZero : Not (S m `LessThanEqual` O)
--nonZeroNotLessThanEqualZero LteZero impossible

--succLte : (S m) `LessThanEqual` (S n) -> m `LessThanEqual` n
--succLte (LteSucc x) = x

minus : N -> N -> N
minus m O = m
minus O n = O
minus (S m) (S n) = minus m n

minusZero : (n : N) -> minus n O = n
minusZero n = Refl

minusSame : (n : N) -> minus n n = O
minusSame O = Refl
minusSame (S n) = rewrite minusSame n in Refl

(-) : (m : N) -> (n : N) -> { auto smaller : n <= m }  -> N
(-) m n {smaller} = minus m n


data NonZero : (n : N) -> Type where
  SuccIsNonZero : NonZero (S n)

--div2 : N -> N -> N -> (N, N)
--div2 s m n = 
 --if m<n then (s, m)
  --      else div2 (S s) (minus n m) n

lte : N -> N -> Bool
lte O     y     = True 
lte (S x) O     = False
lte (S x) (S y) = lte x y

div : N -> (n : N) -> Not (n = O) -> (N, N)
div _ O _ = (O, O)
div m n _ = div' O m
  where
    div' : N -> N -> (N, N)
    div' s m = if lte n m then div' (S s) (m `minus` n)
                          else (s, m)

main : IO ()
main = do
  putStrLn $ "Q.E.D."
  --printLn $ Main.(-) III I { smaller = LteSucc LteZero }
  --printLn $ div VI III SIsNotZero
  --printLn $ getDiff (O `LessThanEqual` IV) 
  --printLn $ (S O) - (S (S (S O)))
  --print $ LessThanEqual I O 
