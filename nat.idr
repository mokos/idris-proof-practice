%hide Nat
%hide Nat.lt
%hide Nat.gt

%default total

対偶 : (a->b) -> (Not b -> Not a)
対偶 hab nb a = nb (hab a)

ならば否定をnandに : (a -> Not b) -> Not (a, b)
ならば否定をnandに anb (a, b) = (anb a) b

nandをならばに : Not (p, q) -> (p -> Not q)
nandをならばに nab p q = nab (p, q)

ならば否定交換 : (a -> Not b) -> (b -> Not a)
ならば否定交換 anb b a = (anb a) b

nand交換 : Not (a, b) -> Not (b, a)
nand交換 nab (b, a) = nab (a, b)

-- Peano axiom 1, 2
data N = O | S N
Show N where
  show O = "0"
  show (S n) = "S" ++ show n

-- Peano axiom 3
zeroIsNotSucc : {n : N} -> Not (O=S(n))
zeroIsNotSucc Refl impossible

succIsNotZero : {n : N} -> Not (S(n)=O)
succIsNotZero Refl impossible

oneIsNotSuccSucc : {n : N} -> Not (S O=S (S n))
oneIsNotSuccSucc Refl impossible

-- Peano axiom 4
succが同じなら同じ : { m, n : N } -> (S m)=(S n) -> m=n
succが同じなら同じ = believe_me "axiom"

違うならsuccも違う : { m, n : N } -> Not (m=n) -> Not (S m=S n)
違うならsuccも違う = 対偶 succが同じなら同じ

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

和がゼロなら両方ゼロ : (m, n : N) -> m + n = O -> (m=O, n=O)
和がゼロなら両方ゼロ O O h = (Refl, Refl)
和がゼロなら両方ゼロ O (S m) h     = void $ (succIsNotZero h)  
和がゼロなら両方ゼロ (S n) O h     = void $ (succIsNotZero h)  
和がゼロなら両方ゼロ (S n) (S m) h = void $ (succIsNotZero h)

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

-- 不等式

data (<) : (m, n : N) -> Type where
  LtZero : O < S n
  LtSucc : m < n -> S m < S n

(>) : (m, n : N) -> Type
m > n = n < m

(<=) : (m, n : N) -> Type
m <= n = Either (m<n) (m=n)

(>=) : (m, n : N) -> Type
m >= n = Either (m>n) (m=n)

infix 0 <>
(<>) : (m, n : N) -> Type
m <> n = Either (m<n) (m>n)

notLtZero : {n : N} -> Not (n<O)
notLtZero _ impossible

-- 不等号の別の定義も同値
infix 0 <.
(<.) : (m, n : N) -> Type
m <. n = (d : N ** m+(S d)=n)

ltImplyLt2 : {m, n : N} -> m<n -> m<.n
ltImplyLt2 {m=O}{n=S d} LtZero = (d ** Refl)
ltImplyLt2 {m=S a}{n=S b} (LtSucc x) with (ltImplyLt2 x)
  | MkDPair d f = MkDPair d (rewrite f in Refl)

lt2ImplyLt : {m, n : N} -> m<.n -> m<n
lt2ImplyLt {m=O} (MkDPair d eq) = rewrite sym eq in LtZero
lt2ImplyLt {m=m}{n=O} (MkDPair d eq) =
  void $ succIsNotZero {n=m+d} (rewrite sym (addSucc m d) in eq)
lt2ImplyLt {m=S a}{n=S b} (MkDPair d eq) =
  LtSucc $ lt2ImplyLt (MkDPair d (succが同じなら同じ eq))


data Either3 a b c = Left a | Middle b | Right c

ltOrEqOrGt : (m, n : N) -> Either3 (m<n) (m=n) (m>n)
ltOrEqOrGt O O = Middle Refl
ltOrEqOrGt O (S n) = Left LtZero
ltOrEqOrGt (S m) O = Right LtZero
ltOrEqOrGt (S a) (S b) with (ltOrEqOrGt a b)
  | Middle eq = Middle (rewrite eq in Refl)
  | Left   lt = Left $ LtSucc lt
  | Right  gt = Right $ LtSucc gt

eqOrIneq : (m, n : N) -> Either (m=n) (m<>n)
eqOrIneq m n with (ltOrEqOrGt m n)
  | Middle eq = Left eq
  | Left   lt = Right $ Left  lt
  | Right  gt = Right $ Right gt

ltImplyNeq : {m, n : N} -> m<n -> Not (m=n)
ltImplyNeq LtZero = zeroIsNotSucc
ltImplyNeq (LtSucc x) = 違うならsuccも違う $ ltImplyNeq x

gtImplyNeq : {m, n : N} -> m>n -> Not (m=n)
gtImplyNeq gt = ltImplyNeq gt . sym

eqOrNeq : (m, n : N) -> Either (m=n) (Not (m=n))
eqOrNeq m n with (ltOrEqOrGt m n)
  | Middle eq = Left eq
  | Left   lt = Right $ ltImplyNeq lt
  | Right  gt = Right $ ltImplyNeq gt . sym

neqImplyIneq : {m, n : N} -> Not (m=n) -> m<>n
neqImplyIneq {m=m}{n=n} h with (ltOrEqOrGt m n)
  | Left lt = Left lt
  | Right gt = Right gt
  | Middle eq = void $ h eq

ineqImplyNeq : {m, n : N} -> m<>n -> Not (m=n)
ineqImplyNeq (Left  lt) = ltImplyNeq lt
ineqImplyNeq (Right gt) = gtImplyNeq gt

notLtAndGt : {m, n : N} -> Not (m<n, m>n) 
notLtAndGt (LtSucc l, LtSucc g) = notLtAndGt (l, g)

ltImplyNgt : {m, n : N} -> m<n -> Not (m>n) 
ltImplyNgt = nandをならばに notLtAndGt

notEqAndLt : {m, n : N} -> Not (m=n, m<n)
notEqAndLt = nand交換 $ ならば否定をnandに ltImplyNeq

notEqAndGt : {m, n : N} -> Not (m=n, m>n)
notEqAndGt = nand交換 $ ならば否定をnandに gtImplyNeq

eqImplyNlt : {m, n : N} -> m=n -> Not (m<n)
eqImplyNlt = nandをならばに notEqAndLt

eqImplyNgt : {m, n : N} -> m=n -> Not (m>n)
eqImplyNgt = nandをならばに notEqAndGt

ltToLte : {m, n : N} -> m<n -> (S m)<=n
ltToLte {m=O}{n=S O} LtZero = Right Refl
ltToLte {m=O}{n=S (S b)} LtZero = Left $ LtSucc $ LtZero
ltToLte (LtSucc x) with (ltToLte x)
  | Left lt = Left $ LtSucc lt
  | Right eq = Right (rewrite eq in Refl)



正整数を足すと大きくなる : (m, n : N) -> m<m+S(n)
正整数を足すと大きくなる O _ = LtZero
正整数を足すと大きくなる (S m) n =
  LtSucc $ 正整数を足すと大きくなる m n

--正整数に1より大をかけると大きくなる :
  --(m, n : N) -> {cond : (m>O, n>I)} -> m<m*n
--正整数に1より大をかけると大きくなる O O impossible



正整数をかけると減らない : {x, y : N} -> x*(S y)>=x
正整数をかけると減らない {x=x}{y=O} = Right $ rewrite mulOne x in Refl
正整数をかけると減らない {x=O}{y=y} = Right $ Refl
正整数をかけると減らない {x=S a}{y=S b} = ?hole
--mulSucc : (m, n : N) -> m * (S n) = m + (m * n)


-- 'x div y' means 'x dividable by y'
div : (x, y : N) -> {auto nz : (x>O, y>O)} -> Type
div x y = (k : N ** (k<=x, x=y*k))

より大きい数では割り切れない :
  {x, y : N} -> {auto nz : (x>O, y>O)} -> x<y -> Not (x `div` y)
より大きい数では割り切れない {y=y}{nz=(xx,yy)} lt div with (div)
  | (MkDPair O (_, f)) = (gtImplyNeq xx) $ rewrite sym (mulZero y) in f
  | (MkDPair (S k) (_, f)) = ?hole

正整数は1で割り切れる : (n : N) -> {nz : n>O} -> n `div` I
正整数は1で割り切れる n = (n ** (Right Refl, rewrite addZero n in Refl))


正整数は自身で割り切れる : (n : N) -> {nz : n>O} -> n `div` n
--正整数は自身で割り切れる n {nz=nz} =
  --(I ** (ltToLte nz, rewrite mulOne n in Refl))
--
--even : (n : N) -> Type
--even n = dividableBy n (S (S O))
--
--isPrime : (n : N) -> Type
--isPrime n = (x : N) -> x>O -> (n `dividableBy` x) -> Either (x=I) (x=n)
--
--twoIsPrime : isPrime (S (S O))
--twoIsPrime O nz h

-- etc
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

main : IO ()
main = do
  putStrLn $ "Q.E.D."
  --printLn $ Main.(-) III I { smaller = LteSucc LteZero }

