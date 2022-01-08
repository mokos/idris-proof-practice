%hide (||)
%default total

-- logic

-- 同値
infix 0 <=>
(<=>) : Type -> Type -> Type
p <=> q = (p->q, q->p)

data (||) a b = L a | R b

xor : Type -> Type -> Type
xor a b = (a, Not b) || (b, Not a)

infixr 3 /\
(/\) : Type -> Type -> Type
a /\ b = (a, b)

--infixr 3 \/
--data (\/) a b = L a | R b

ならば否定をnandに : (a -> Not b) -> Not (a, b)
ならば否定をnandに anb (a, b) = (anb a) b

nandをならば否定に : Not (p, q) -> (p -> Not q)
nandをならば否定に nab p q = nab (p, q)

ならば否定交換 : (a -> Not b) -> (b -> Not a)
ならば否定交換 anb b a = (anb a) b


-- not equal
(/=) : a -> a -> Type
x /= y = Not (x=y)

symnot : a /= b -> b /= a
symnot abn ba = abn $ sym ba

-- 自然数
--- ペアノの公理 1, 2
prefix 9 `S`

data N = O | S N
Show N where
  show O = "0"
  show (S n) = "S" ++ show n

--- ペアノの公理 3
zeroIsNotSucc : {n : N} -> O /= S n
zeroIsNotSucc Refl impossible

succIsNotZero : {n : N} -> S n /= O
succIsNotZero = symnot zeroIsNotSucc

--- ペアノの公理 4
違うならsuccも違う : {m, n : N} -> m/=n -> S m/=S n
違うならsuccも違う = believe_me "axiom"

-- 自然数の等号の排中律
eqOrNeq : (m, n : N) -> (m=n) || (m/=n)
eqOrNeq O O = L Refl
eqOrNeq O (S n) = R zeroIsNotSucc
eqOrNeq (S m) O = R succIsNotZero
eqOrNeq (S m) (S n) with (eqOrNeq m n)
  | L eq  = L $ cong eq
  | R neq = R $ 違うならsuccも違う neq

succが同じなら同じ : {m, n : N} -> S m=S n -> m=n
succが同じなら同じ {m}{n} h with (eqOrNeq m n)
  | L eq  = eq
  | R neq = void $ 違うならsuccも違う neq $ h



(+) : N -> N -> N
O     + n = n
(S m) + n = S (m + n)

(*) : N -> N -> N
O     * n = O
(S m) * n = n + (m * n)

I : N
I = S O

add0 : (n : N) -> n + O = n
add0 O = Refl
add0 (S k) = rewrite add0 k in Refl

addSucc : (m, n : N) -> m + S n = S (m + n)
addSucc O n = Refl
addSucc (S m) n = rewrite addSucc m n in Refl

add交換則 : (m, n : N) -> m + n = n + m
add交換則 O n = rewrite add0 n in Refl
add交換則 (S m) n =
  rewrite addSucc n m in
  rewrite add交換則 m n in
  Refl 

add結合則 : (a, b, c : N) -> (a + b) + c = a + (b + c)
add結合則 O b c = Refl
add結合則 (S a) b c = rewrite add結合則 a b c in Refl

x0 : (n : N) -> n * O = O
x0 O = Refl
x0 (S n) = rewrite x0 n in Refl

lx : (n : N) -> I * n = n
lx O = Refl
lx (S n) = rewrite lx n in Refl

x1 : (n : N) -> n * I = n
x1 O = Refl
x1 (S n) = rewrite x1 n in Refl

xSucc : (m, n : N) -> m * S n = m + (m * n)
xSucc O n = Refl
xSucc (S m) n =
  rewrite xSucc m n in 
  rewrite sym $ add結合則 m n (m * n) in
  rewrite sym $ add結合則 n m (m * n) in
  rewrite add交換則 n m in
  Refl

mul交換則 : (m, n : N) -> m * n = n * m
mul交換則 O n = rewrite x0 n in Refl
mul交換則 (S m) n = 
  rewrite xSucc n m in
  rewrite mul交換則 m n in
  Refl

分配則 : (a, b, c : N) -> (a+b) * c = a*c + b*c
分配則 O b c = Refl
分配則 (S a) b c =
  rewrite 分配則 a b c in
  rewrite add結合則 c (a*c) (b*c) in 
  Refl

分配則' : (a : N) -> (b : N) -> (c : N) -> a * (b+c) = a*b + a*c
分配則' a b c =
  rewrite mul交換則 a (b+c) in
  rewrite 分配則 b c a in
  rewrite mul交換則 b a in
  rewrite mul交換則 c a in
  Refl

mul結合則 : (a, b, c : N) -> (a * b) * c = a * (b * c)
mul結合則 O b c = Refl
mul結合則 (S a) b c = 
  rewrite 分配則 b (a*b) c in
  rewrite mul結合則 a b c in
  Refl

和が0なら両方0 : (m, n : N) -> m+n=O -> (m=O, n=O)
和が0なら両方0 O O h = (Refl, Refl)
和が0なら両方0 O (S m) h     = void $ (succIsNotZero h)  
和が0なら両方0 (S n) O h     = void $ (succIsNotZero h)  
和が0なら両方0 (S n) (S m) h = void $ (succIsNotZero h)

-- 不等式

data (<) : (m, n : N) -> Type where
  Lt0 : O < S n
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

notLt0 : {n : N} -> Not (n<O)
notLt0 _ impossible

-- 不等号の別の定義
infix 4 <.
(<.) : (m, n : N) -> Type
m <. n = (d : N ** m + S d = n)

infix 4 <=.
(<=.) : (m, n : N) -> Type
m <=. n = (d : N ** m + d = n)

lt2ImplyLte2 : {m, n : N} -> m<.n -> m<=.n
lt2ImplyLte2 (d ** eq) = (S d ** eq)

ltImplyLt2 : {m, n : N} -> m<n -> m<.n
ltImplyLt2 {m=O}{n=S d} Lt0 = (d ** Refl)
ltImplyLt2 {m=S a}{n=S b} (LtSucc x) with (ltImplyLt2 x)
  | (d ** f) = (d ** rewrite f in Refl)

lt2ImplyLt : {m, n : N} -> m<.n -> m<n
lt2ImplyLt {m=O} (d ** eq) = rewrite sym eq in Lt0
lt2ImplyLt {m}{n=O} (d ** eq) =
  void $ succIsNotZero {n=m+d} (rewrite sym (addSucc m d) in eq)
lt2ImplyLt {m=S a}{n=S b} (d ** eq) =
  LtSucc $ lt2ImplyLt (d ** succが同じなら同じ eq)

lteImplyLte2 : {m, n : N} -> m<=n -> m<=.n
lteImplyLte2 {m}{n} (R eq) = (O ** rewrite eq in rewrite add0 n in Refl)
lteImplyLte2 {m}{n} (L lt) = lt2ImplyLte2 $ ltImplyLt2 lt

lte2ImplyLte : {m, n : N} -> m<=.n -> m<=n
lte2ImplyLte {m} (O ** eq) = R $ rewrite sym eq in rewrite add0 m in Refl
lte2ImplyLte {m} (S d ** eq) = L $ lt2ImplyLt (d ** eq)

小なりの2つの定義は同値 : {m, n : N} -> m<n <=> m<.n
小なりの2つの定義は同値 = (ltImplyLt2, lt2ImplyLt)

小なりイコールの2つの定義は同値 : {m, n : N} -> m<=n <=> m<=.n
小なりイコールの2つの定義は同値 = (lteImplyLte2, lte2ImplyLte)

--以下の2つの定義は同値 : {m, n : N} -> m<=.n <=>

lt推移律 : {x, y, z: N} -> x<y /\ y<z -> x<z
lt推移律 (_, Lt0) impossible
lt推移律 (Lt0, LtSucc yz) = Lt0
lt推移律 (LtSucc xy, LtSucc yz) = LtSucc $ lt推移律 (xy, yz)

lt2推移律 : {x, y, z : N} -> (x<.y, y<.z) -> x<.z
lt2推移律 (xy, yz) = 
  ltImplyLt2 $ lt推移律 (lt2ImplyLt xy, lt2ImplyLt yz)

lte2推移律 : {x, y, z : N} -> (x<=.y, y<=.z) -> x<=.z
lte2推移律 {x} ((d ** eq), (e ** eq2)) =
  ((d+e) ** rewrite sym $ add結合則 x d e in rewrite eq in eq2)

lte推移律 : {x, y, z : N} -> (x<=y, y<=z) -> x<=z
lte推移律 (xy, yz) = 
  lte2ImplyLte $ lte2推移律 (lteImplyLte2 xy, lteImplyLte2 yz)


eqOrIneq : (m, n : N) -> (m=n) || (m<>n)
eqOrIneq O O = L Refl
eqOrIneq O (S n) = R $ L Lt0
eqOrIneq (S m) O = R $ R Lt0
eqOrIneq (S a) (S b) with (eqOrIneq a b)
  | L eq = L $ rewrite eq in Refl
  | R (L lt) = R $ L $ LtSucc lt
  | R (R gt) = R $ R $ LtSucc gt

ltImplyNeq : {m, n : N} -> m<n -> Not (m=n)
ltImplyNeq Lt0 = zeroIsNotSucc
ltImplyNeq (LtSucc x) = 違うならsuccも違う $ ltImplyNeq x

gtImplyNeq : {m, n : N} -> m>n -> Not (m=n)
gtImplyNeq gt = ltImplyNeq gt . sym

neqImplyIneq : {m, n : N} -> Not (m=n) -> m<>n
neqImplyIneq {m}{n} h with (eqOrIneq m n)
  | L eq = void $ h eq
  | R (L lt) = L lt
  | R (R gt) = R gt

ineqImplyNeq : {m, n : N} -> m<>n -> Not (m=n)
ineqImplyNeq (L lt) = ltImplyNeq lt
ineqImplyNeq (R gt) = gtImplyNeq gt

notLtAndGt : {m, n : N} -> Not (m<n, m>n) 
notLtAndGt (LtSucc l, LtSucc g) = notLtAndGt (l, g)

ltImplyNgt : {m, n : N} -> m<n -> Not (m>n) 
ltImplyNgt = nandをならば否定に notLtAndGt

eqImplyNlt : {m, n : N} -> m=n -> Not (m<n)
eqImplyNlt = ならば否定交換 ltImplyNeq

eqImplyNgt : {m, n : N} -> m=n -> Not (m>n)
eqImplyNgt = ならば否定交換 gtImplyNeq

ltToLte : {m, n : N} -> m<n -> (S m)<=n
ltToLte {m=O}{n=S O} Lt0 = R Refl
ltToLte {m=O}{n=S S b} Lt0 = L $ LtSucc $ Lt0
ltToLte (LtSucc x) with (ltToLte x)
  | L lt = L $ LtSucc lt
  | R eq = R $ rewrite eq in Refl

notLtSelf : {n : N} -> Not (n<n)
notLtSelf = eqImplyNlt Refl

zeroOrGtZero : (n : N) -> (n=O) || (n>O)
zeroOrGtZero O = L Refl
zeroOrGtZero (S n) = R Lt0

正整数を足すと大きくなる : (n, p : N) -> {auto nz : p>O} -> n<n+p
正整数を足すと大きくなる _ O {nz} = void $ notLt0 nz
正整数を足すと大きくなる n (S d) = lt2ImplyLt (d ** Refl)

ltAddNat : {k, m, n : N} -> m<n -> m+k<n+k
ltAddNat {k=O}{m}{n} lt = rewrite add0 n in rewrite add0 m in lt
ltAddNat {k=S a}{m=O}{n=S c} Lt0 =
  rewrite add交換則 (S c) (S a) in
  正整数を足すと大きくなる (S a) (S c)
ltAddNat (LtSucc x) = LtSucc $ ltAddNat x 

ltMulPos : {m, n, k : N} -> {auto nz : k>O} -> m<n -> m*k<n*k
ltMulPos {k=O}{nz=nz} _ = void $ notLt0 nz
ltMulPos {k=S a}{n=O} lt = void $ notLt0 lt
ltMulPos {k=S a}{m=O}{n=S c} lt = Lt0
ltMulPos {k=k}{m=S b}{n=S c} (LtSucc x) =
  rewrite add交換則 k (c*k) in
  rewrite add交換則 k (b*k) in
  ltAddNat {k=k} (ltMulPos {k=k}{m=b}{n=c} x)

大きい方に足しても大きい : {m, n : N} -> m<n -> (k : N) -> m<n+k
大きい方に足しても大きい Lt0 k = Lt0
大きい方に足しても大きい (LtSucc x) k =
  LtSucc $ 大きい方に足しても大きい x k

大きい方に正整数をかけても大きい :
  {m, n : N} -> m<n -> (p : N) -> {auto nz : p>O} -> m<n*p
大きい方に正整数をかけても大きい _ O impossible
大きい方に正整数をかけても大きい {n} lt (S p) = 
  rewrite xSucc n p in 大きい方に足しても大きい lt (n*p)


正整数に2以上をかけると大きくなる :
  (m, n : N) -> {auto c : (m>O, n>I)} -> m<m*n
正整数に2以上をかけると大きくなる m n {c=(m1, n2)} =
  rewrite mul交換則 m n in
  rewrite sym $ lx m in
  rewrite sym $ mul結合則 n (S O) m in
  rewrite x1 n in
  ltMulPos {k=m} n2

正整数をかけると減らない : {n, p : N} -> {auto nz : p>O} -> n<=n*p
正整数をかけると減らない {p=O} impossible
正整数をかけると減らない {n=O} = R $ Refl
正整数をかけると減らない {n}{p=S O} = R $ rewrite x1 n in Refl
正整数をかけると減らない {n=S a}{p=S S b} = 
  L $ 正整数に2以上をかけると大きくなる (S a) (S S b)


--f : (m, n : N) -> m*n=I -> m=I
--f O n eq = void $ zeroIsNotSucc eq
--f m O eq = void $ zeroIsNotSucc $ rewrite x0 m in eq



-- 'x div y' means 'x dividable by y'
div : (x, y : N) -> Type
div x y = (k : N ** x=y*k)
  
正整数は1で割り切れる : (p : N) -> {auto nz : p>O} -> p `div` I
正整数は1で割り切れる p = (p ** rewrite add0 p in Refl)

ゼロは自然数で割り切れる : (n : N) -> O `div` n
ゼロは自然数で割り切れる n = (O ** rewrite x0 n in Refl)

正整数は自身で割り切れる : (p : N) -> {auto nz : p>O} -> p `div` p
正整数は自身で割り切れる p {nz} = (I ** rewrite x1 p in Refl)

正整数を割り切れるのはそれ以下の正整数 :
  {x, y, z : N} -> {auto nz : x>O} -> x=y*z -> (O<z, z<=x)
正整数を割り切れるのはそれ以下の正整数 {x}{y}{z}{nz} xyz
  with (zeroOrGtZero y)
  | L y0 = void $ eqImplyNgt xyz $ rewrite y0 in nz
  | R yp
    with (zeroOrGtZero z)
    | L z0 = void $ eqImplyNgt xyz $ rewrite z0 in rewrite x0 y in nz
    | R zp
      with (eqOrIneq z x)
      | L eq = (zp, R eq)
      | R (L lt) = (zp, L lt)
      | R (R gt) = void $ eqImplyNlt xyz $ rewrite mul交換則 y z in
                                           大きい方に正整数をかけても大きい gt y

正整数を割り切れるのはそれ以下の正整数' :
  {x, y, z : N} -> {auto nz : x>O} -> x=y*z -> (O<y, y<=x)
正整数を割り切れるのはそれ以下の正整数' {y=y}{z=z} xyz =
  正整数を割り切れるのはそれ以下の正整数 {y=z}{z=y} 
    (rewrite mul交換則 z y in xyz)

--prime' : (x : N) -> Type

prime : (x : N) -> Type
prime x = (y : N) -> (x `div` y) -> xor (y=I) (y=x)

zeroIsNotPrime : Not (prime O)
zeroIsNotPrime f with (f (S S O) (ゼロは自然数で割り切れる (S S O)))
  | L (eq, neq) = 違うならsuccも違う succIsNotZero $ eq
  | R (eq, neq) = succIsNotZero eq

oneIsNotPrime : Not (prime I) 
oneIsNotPrime f with (f I (正整数は1で割り切れる I))
  | L (eq, neq) = neq eq
  | R (eq, neq) = neq eq

twoIsPrime : prime (S S O)
twoIsPrime y (z ** f)
  with (正整数を割り切れるのはそれ以下の正整数' f)
  | (yp, R eq) = R (eq, rewrite eq in gtImplyNeq $ LtSucc Lt0)
  | (yp, L lt) 
    with (y)
    | O = void $ notLt0 yp
    | S O = L (Refl, ltImplyNeq $ LtSucc Lt0)
    | (S S a)
      with (lt)
      | (LtSucc (LtSucc x)) = void $ notLt0 x

-- etc
pow : N -> N -> N
pow m O     = I
pow m (S n) = m * (pow m n)

pow1 : (n : N) -> pow n I = n
pow1 n = rewrite x1 n in Refl

onePow : (n : N) -> pow I n = I
onePow O = Refl
onePow (S n) = rewrite onePow n in Refl

指数法則1 : (a, m, n : N) -> (pow a m) * (pow a n) = pow a (m+n)
指数法則1 a O n = rewrite add0 (pow a n) in Refl
指数法則1 a (S m) n =
  rewrite sym $ 指数法則1 a m n in
  rewrite mul結合則 a (pow a m) (pow a n) in
  Refl

指数法則2 : (a, m, n : N) -> pow (pow a m) n = pow a (m*n)
指数法則2 a O n = rewrite onePow n in Refl
指数法則2 a m O = rewrite x0 m in Refl
指数法則2 a m (S n) =
  rewrite xSucc m n in
  rewrite sym $ 指数法則1 a m (m*n) in
  rewrite 指数法則2 a m n in
  Refl

指数法則3 : (a, b, n : N) -> pow (a*b) n = (pow a n) * (pow b n)
指数法則3 a b O = Refl
指数法則3 a b (S n) =
  rewrite 指数法則3 a b n in
  rewrite mul結合則 a (pow a n) (b * pow b n) in
  rewrite mul結合則 a b (pow a n * pow b n) in
  rewrite sym $ mul結合則 (pow a n) b (pow b n) in
  rewrite sym $ mul結合則 b (pow a n) (pow b n) in
  rewrite mul交換則 b (pow a n) in
  Refl

main : IO ()
main = do
  putStrLn $ "Q.E.D."
