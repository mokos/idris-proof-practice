%hide Nat
%hide Nat.lt
%hide Nat.gt
%hide (||)

%default total

data (||) a b = L a | R b

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
succが同じなら同じ : {m, n : N} -> S m=S n -> m=n
succが同じなら同じ = believe_me "axiom"

違うならsuccも違う : {m, n : N} -> Not (m=n) -> Not (S m=S n)
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
m <= n = (m<n) || (m=n)

(>=) : (m, n : N) -> Type
m >= n = (m>n) || (m=n)

infix 4 <>
(<>) : (m, n : N) -> Type
m <> n = (m<n) || (m>n)

notLtZero : {n : N} -> Not (n<O)
notLtZero _ impossible

-- 不等号の別の定義も同値
infix 4 <.
(<.) : (m, n : N) -> Type
m <. n = (d : N ** m+(S d)=n)

--E : Type

ltImplyLt2 : {m, n : N} -> m<n -> m<.n
ltImplyLt2 {m=O}{n=S d} LtZero = (d ** Refl)
ltImplyLt2 {m=S a}{n=S b} (LtSucc x) with (ltImplyLt2 x)
  | (d ** f) = (d ** rewrite f in Refl)

lt2ImplyLt : {m, n : N} -> m<.n -> m<n
lt2ImplyLt {m=O} (d ** eq) = rewrite sym eq in LtZero
lt2ImplyLt {m=m}{n=O} (d ** eq) =
  void $ succIsNotZero {n=m+d} (rewrite sym (addSucc m d) in eq)
lt2ImplyLt {m=S a}{n=S b} (d ** eq) =
  LtSucc $ lt2ImplyLt (d ** succが同じなら同じ eq)

eqOrIneq : (m, n : N) -> (m=n) || (m<>n)
eqOrIneq O O = L Refl
eqOrIneq O (S n) = R $ L LtZero
eqOrIneq (S m) O = R $ R LtZero
eqOrIneq (S a) (S b) with (eqOrIneq a b)
  | L eq = L $ rewrite eq in Refl
  | R (L lt) = R $ L $ LtSucc lt
  | R (R gt) = R $ R $ LtSucc gt

ltImplyNeq : {m, n : N} -> m<n -> Not (m=n)
ltImplyNeq LtZero = zeroIsNotSucc
ltImplyNeq (LtSucc x) = 違うならsuccも違う $ ltImplyNeq x

gtImplyNeq : {m, n : N} -> m>n -> Not (m=n)
gtImplyNeq gt = ltImplyNeq gt . sym

eqOrNeq : (m, n : N) -> (m=n) || (Not (m=n))
eqOrNeq m n with (eqOrIneq m n)
  | L eq = L eq
  | R (L lt) = R $ ltImplyNeq lt
  | R (R gt) = R $ ltImplyNeq gt . sym

neqImplyIneq : {m, n : N} -> Not (m=n) -> m<>n
neqImplyIneq {m=m}{n=n} h with (eqOrIneq m n)
  | L eq = void $ h eq
  | R (L lt) = L lt
  | R (R gt) = R gt

ineqImplyNeq : {m, n : N} -> m<>n -> Not (m=n)
ineqImplyNeq (L lt) = ltImplyNeq lt
ineqImplyNeq (R gt) = gtImplyNeq gt

notLtAndGt : {m, n : N} -> Not (m<n, m>n) 
notLtAndGt (LtSucc l, LtSucc g) = notLtAndGt (l, g)

ltImplyNgt : {m, n : N} -> m<n -> Not (m>n) 
ltImplyNgt = nandをならばに notLtAndGt

eqImplyNlt : {m, n : N} -> m=n -> Not (m<n)
eqImplyNlt = ならば否定交換 ltImplyNeq

eqImplyNgt : {m, n : N} -> m=n -> Not (m>n)
eqImplyNgt = ならば否定交換 gtImplyNeq

ltToLte : {m, n : N} -> m<n -> (S m)<=n
ltToLte {m=O}{n=S O} LtZero = R Refl
ltToLte {m=O}{n=S (S b)} LtZero = L $ LtSucc $ LtZero
ltToLte (LtSucc x) with (ltToLte x)
  | L lt = L $ LtSucc lt
  | R eq = R $ rewrite eq in Refl


notLtSelf : {n : N} -> Not (n<n)
notLtSelf = eqImplyNlt Refl

zeroOrGtZero : (n : N) -> (n=O) || (n>O)
zeroOrGtZero O = L Refl
zeroOrGtZero (S n) = R LtZero

正整数を足すと大きくなる : (n, p : N) -> {auto nz : p>O} -> n<n+p
正整数を足すと大きくなる _ O {nz=nz} = void $ notLtZero nz
正整数を足すと大きくなる n (S d) = lt2ImplyLt (d ** Refl)

ltAddNat : {k, m, n : N} -> m<n -> m+k<n+k
ltAddNat {k=O}{m=m}{n=n} lt = rewrite addZero n in rewrite addZero m in lt
ltAddNat {k=S a}{m=O}{n=S c} LtZero =
  rewrite 加法交換則 (S c) (S a) in
  正整数を足すと大きくなる (S a) (S c)
ltAddNat (LtSucc x) = LtSucc $ ltAddNat x 

ltMulPos : {m, n, k : N} -> {auto nz : k>O} -> m<n -> m*k<n*k
ltMulPos {k=O}{nz=nz} _ = void $ notLtZero nz
ltMulPos {k=S a}{n=O} lt = void $ notLtZero lt
ltMulPos {k=S a}{m=O}{n=S c} lt = LtZero
ltMulPos {k=k}{m=S b}{n=S c} (LtSucc x) =
  rewrite 加法交換則 k (c*k) in
  rewrite 加法交換則 k (b*k) in
  ltAddNat {k=k} (ltMulPos {k=k}{m=b}{n=c} x)

大に足しても大 : {m, n : N} -> m<n -> (k : N) -> m<n+k
大に足しても大 LtZero k = LtZero
大に足しても大 (LtSucc x) k = LtSucc $ 大に足しても大 x k

大に正整数をかけても大 :
  {m, n : N} -> m<n -> (p : N) -> {auto nz : p>O} -> m<n*p
大に正整数をかけても大 _ O impossible
大に正整数をかけても大 {n=n} lt (S p) = 
  rewrite mulSucc n p in 大に足しても大 lt (n*p)


正整数に2以上をかけると大きくなる :
  (m, n : N) -> {auto cond : (m>O, n>I)} -> m<m*n
正整数に2以上をかけると大きくなる m n {cond=(m1, n2)} =
  rewrite 乗法交換則 m n in
  rewrite sym $ oneMul m in
  rewrite sym $ 乗法結合則 n (S O) m in
  rewrite mulOne n in
  ltMulPos {k=m} n2

正整数をかけると減らない : {n, p : N} -> {auto nz : p>O} -> n<=n*p
正整数をかけると減らない {p=O} impossible
正整数をかけると減らない {n=O} = R $ Refl
正整数をかけると減らない {n=n}{p=S O} = R $ rewrite mulOne n in Refl
正整数をかけると減らない {n=S a}{p=S (S b)} = 
  L $ 正整数に2以上をかけると大きくなる (S a) (S (S b))


-- 'x div y' means 'x dividable by y'
div : (x, y : N) -> {auto nz : (x>O, y>O)} -> Type
div x y = (k : N ** x=y*k)
  
正整数は1で割り切れる : (p : N) -> {auto nz : p>O} -> p `div` I
正整数は1で割り切れる p = (p ** rewrite addZero p in Refl)

正整数は自身で割り切れる : (p : N) -> {auto nz : p>O} -> p `div` p
正整数は自身で割り切れる p {nz=nz} = (I ** rewrite mulOne p in Refl)

正整数を割り切れるのはそれ以下の正整数 :
  {x, y, z : N} -> {auto nz : x>O} -> x=y*z -> (O<z, z<=x)
正整数を割り切れるのはそれ以下の正整数 {x=x}{y=y}{z=z}{nz=nz} xyz
  with (zeroOrGtZero y)
  | L y0 = void $ eqImplyNgt xyz $ rewrite y0 in nz
  | R yp
    with (zeroOrGtZero z)
    | L z0 = void $ eqImplyNgt xyz $ rewrite z0 in rewrite mulZero y in nz
    | R zp
      with (eqOrIneq z x)
      | L eq = (zp, R eq)
      | R (L lt) = (zp, L lt)
      | R (R gt) = void $ eqImplyNlt xyz $ rewrite 乗法交換則 y z in
                                           大に正整数をかけても大 gt y

--
--even : (n : N) -> Type
--even n = dividableBy n (S (S O))

--isPrime : (n : N) -> Type
--isPrime n = (x : N) -> x>O -> (n `div` x) -> (x=I) || (x=n)

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

main : IO ()
main = do
  putStrLn $ "Q.E.D."
