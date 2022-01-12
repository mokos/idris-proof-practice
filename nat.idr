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

ならば否定交換 : (a -> Not b) -> (b -> Not a)
ならば否定交換 anb b a = (anb a) b

-- not equal
(/=) : a -> a -> Type
x /= y = Not (x=y)

symnot : a /= b -> b /= a
symnot abn ba = abn $ sym ba

-- 自然数
--- ペアノの公理 1, 2
prefix 99 `S`

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

-- cong
同じなら関数適用しても同じ : {f : a->b} -> {x, y : a} -> x=y -> f x = f y
同じなら関数適用しても同じ {f}{x}{y} eq = rewrite eq in Refl

-- 自然数の同値関係の排中律
eqOrNeq : (m, n : N) -> (m=n) || (m/=n)
eqOrNeq O O = L Refl
eqOrNeq O (S n) = R zeroIsNotSucc
eqOrNeq (S m) O = R succIsNotZero
eqOrNeq (S m) (S n) with (eqOrNeq m n)
  | L eq  = L $ 同じなら関数適用しても同じ eq
  | R neq = R $ 違うならsuccも違う neq

-- ペアノの公理4の対偶
succが同じなら同じ : {m, n : N} -> S m=S n -> m=n
succが同じなら同じ {m}{n} h with (eqOrNeq m n)
  | L eq  = eq
  | R neq = void $ 違うならsuccも違う neq $ h



-- add
(+) : N -> N -> N
O     + n = n
(S m) + n = S (m + n)

-- mul
(*) : N -> N -> N
O     * n = O
(S m) * n = n + (m * n)

-- one
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

-- x means *
x0 : (n : N) -> n * O = O
x0 O = Refl
x0 (S n) = rewrite x0 n in Refl

-- l means one
n1X : (n : N) -> I * n = n
n1X O = Refl
n1X (S n) = rewrite n1X n in Refl

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

積が1なら両方1 : (m, n : N) -> m*n=I -> (m=I, n=I)
積が1なら両方1 O n eq = void $ zeroIsNotSucc eq
積が1なら両方1 m O eq = void $ zeroIsNotSucc $ rewrite sym $ x0 m in eq
積が1なら両方1 (S O) (S O)   eq = (Refl, Refl)
積が1なら両方1 (S S m) (S O) eq =
  void $ 違うならsuccも違う succIsNotZero $ eq
積が1なら両方1 (S m) (S S n) eq =
  void $ 違うならsuccも違う succIsNotZero $ eq

積が0なら片方は0 : {m, n : N} -> m*n=O -> (m=O) || (n=O)
積が0なら片方は0 {m=O} _ = L Refl
積が0なら片方は0 {n=O} _ = R Refl
積が0なら片方は0 {m=S m}{n=S n} eq = void $ succIsNotZero eq


-- 不等式

data (<) : (m, n : N) -> Type where
  Lt0 : O < S n
  LtSucc : m < n -> S m < S n

(>) : (m, n : N) -> Type
m > n = n < m

(<=) : (m, n : N) -> Type
m <= n = (m<n) || (m=n)

(>=) : (m, n : N) -> Type
m >= n = n <= m

infix 4 <>
(<>) : (m, n : N) -> Type
m <> n = (m<n) || (m>n)

notLt0 : {n : N} -> Not (n<O)
notLt0 _ impossible

-- 不等号の別の定義
infix 4 <., >., <=., >=.
(<.) : (m, n : N) -> Type
m <. n = (d : N ** m + S d = n)

(>.) : (m, n : N) -> Type
m >. n = n <. m

(<=.) : (m, n : N) -> Type
m <=. n = (d : N ** m + d = n)

(>=.) : (m, n : N) -> Type
m >=. n = n <=. m

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

ltImplyNeq : {m, n : N} -> m<n -> m/=n
ltImplyNeq Lt0 = zeroIsNotSucc
ltImplyNeq (LtSucc x) = 違うならsuccも違う $ ltImplyNeq x

gtImplyNeq : {m, n : N} -> m>n -> m/=n
gtImplyNeq gt = ltImplyNeq gt . sym

ineqImplyNeq : {m, n : N} -> m<>n -> m/=n
ineqImplyNeq (L lt) = ltImplyNeq lt
ineqImplyNeq (R gt) = gtImplyNeq gt

neqImplyIneq : {m, n : N} -> m/=n -> m<>n
neqImplyIneq {m}{n} h with (eqOrIneq m n)
  | L eq = void $ h eq
  | R (L lt) = L lt
  | R (R gt) = R gt

ltImplyNgt : {m, n : N} -> m<n -> Not (m>n) 
ltImplyNgt (LtSucc l) (LtSucc g) = ltImplyNgt l g

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
  rewrite add交換則 (S c) (S a) in 正整数を足すと大きくなる (S a) (S c)
ltAddNat (LtSucc x) = LtSucc $ ltAddNat x 

ltMulPos : {m, n, k : N} -> {auto nz : k>O} -> m<n -> m*k<n*k
ltMulPos {k=O}{nz=nz} _ = void $ notLt0 nz
ltMulPos {k=S a}{n=O} lt = void $ notLt0 lt
ltMulPos {k=S a}{m=O}{n=S c} lt = Lt0
ltMulPos {k}{m=S b}{n=S c} (LtSucc x) =
  rewrite add交換則 k (c*k) in
  rewrite add交換則 k (b*k) in
  ltAddNat {k} (ltMulPos {k}{m=b}{n=c} x)

ltMulNat : {m, n, k : N} -> m<n -> m*k<=n*k
ltMulNat {m}{n}{k=O} _ = R $ rewrite x0 n in rewrite sym $ x0 m in Refl
ltMulNat {m}{n}{k=S k} lt = L $ ltMulPos lt

lteMulNat : {m, n, k : N} -> m<=n -> m*k<=n*k
lteMulNat (R eq) = R $ rewrite eq in Refl
lteMulNat (L lt) = ltMulNat lt

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
  rewrite sym $ n1X m in
  rewrite sym $ mul結合則 n (S O) m in
  rewrite x1 n in
  ltMulPos {k=m} n2

正整数をかけると減らない : {n, p : N} -> {auto nz : p>O} -> n<=n*p
正整数をかけると減らない {p=O} impossible
正整数をかけると減らない {n=O} = R $ Refl
正整数をかけると減らない {n}{p=S O} = R $ rewrite x1 n in Refl
正整数をかけると減らない {n=S a}{p=S S b} = 
  L $ 正整数に2以上をかけると大きくなる (S a) (S S b)


-- 'd |. n' means 'd devides n'
infix 5 |.
(|.) : (d, n : N) -> Type
d |. n = (k : N ** n=d*k)
  
正整数は1で割り切れる : (p : N) -> {auto nz : p>O} -> I |. p
正整数は1で割り切れる p = (p ** rewrite add0 p in Refl)

ゼロは自然数で割り切れる : (n : N) -> n |. O
ゼロは自然数で割り切れる n = (O ** rewrite x0 n in Refl)

正整数は自身で割り切れる : (p : N) -> {auto nz : p>O} -> p |. p
正整数は自身で割り切れる p {nz} = (I ** rewrite x1 p in Refl)

正整数を割り切れるのはそれ以下の正整数 :
  {n, d, k : N} -> {auto nz : n>O} -> n=d*k -> (O<k, k<=n)
正整数を割り切れるのはそれ以下の正整数 {n}{d}{k}{nz} ndk
  with (zeroOrGtZero d)
  | L d0 = void $ eqImplyNgt ndk $ rewrite d0 in nz
  | R dp
    with (zeroOrGtZero k)
    | L k0 = void $ eqImplyNgt ndk $ rewrite k0 in rewrite x0 d in nz
    | R kp
      with (eqOrIneq k n)
      | L eq = (kp, R eq)
      | R (L lt) = (kp, L lt)
      | R (R gt) =
          void $ eqImplyNlt ndk $ rewrite mul交換則 d k in
                                  大きい方に正整数をかけても大きい gt d

正整数を割り切れるのはそれ以下の正整数' :
  {n, d, k : N} -> {auto nz : n>O} -> n=d*k -> (O<d, d<=n)
正整数を割り切れるのはそれ以下の正整数' {d}{k} ndk =
  正整数を割り切れるのはそれ以下の正整数 {d=k}{k=d} 
    (rewrite mul交換則 k d in ndk)

--prime' : (x : N) -> Type

prime : (x : N) -> Type
prime x = (d : N) -> (d |. x) -> xor (d=I) (d=x)

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

-- べき乗
infixr 10 ^
(^) : N -> N -> N
m ^ O     = I
m ^ (S n) = m * m^n

pow1 : (n : N) -> n^I = n
pow1 n = rewrite x1 n in Refl

onePow : (n : N) -> I^n = I
onePow O = Refl
onePow (S n) = rewrite onePow n in Refl

指数法則1 : (a, m, n : N) -> a^m * a^n = a^(m+n)
指数法則1 a O n = rewrite add0 (a^n) in Refl
指数法則1 a (S m) n =
  rewrite sym $ 指数法則1 a m n in
  rewrite mul結合則 a (a^m) (a^n) in
  Refl

指数法則2 : (a, m, n : N) -> (a^m)^n = a^(m*n)
指数法則2 a O n = rewrite onePow n in Refl
指数法則2 a m O = rewrite x0 m in Refl
指数法則2 a m (S n) =
  rewrite xSucc m n in
  rewrite sym $ 指数法則1 a m (m*n) in
  rewrite 指数法則2 a m n in
  Refl

指数法則3 : (a, b, n : N) -> (a*b)^n = a^n * b^n
指数法則3 a b O = Refl
指数法則3 a b (S n) =
  rewrite 指数法則3 a b n in
  rewrite mul結合則 a (a^n) (b * b^n) in
  rewrite mul結合則 a b (a^n * b^n) in
  rewrite sym $ mul結合則 (a^n) b (b^n) in
  rewrite sym $ mul結合則 b (a^n) (b^n) in
  rewrite mul交換則 b (a^n) in
  Refl


互いに素 : (x, y : N) -> Type
互いに素 x y = {d : N} -> (x |. d, y |. d) -> d=I

-- ユークリッドの補題
--f : (p : N) -> {c : prime p} -> (a*b) |. p -> a |. p || b |. p

modEq : (n, x, y : N) -> Type
modEq n x y = (a : N ** b : N ** x+n*a = y+n*b)

modEq反射律 : {n, x, y : N} -> modEq n x y -> modEq n y x
modEq反射律 (a ** b ** f) = (b ** a ** sym f)

modEq推移律 : {n, x, y, z : N} -> (modEq n x y, modEq n y z) -> modEq n x z
modEq推移律 {n}{x}{y}{z} ((a ** b ** xy), (c ** d ** yz)) =
  ((a+c) ** (b+d) ** (
    rewrite add交換則 b d in
    rewrite 分配則' n d b in
    rewrite sym $ add結合則 z (n*d) (n*b) in
    rewrite sym yz in
    rewrite add結合則 y (n*c) (n*b) in
    rewrite add交換則 (n*c) (n*b) in
    rewrite sym $ add結合則 y (n*b) (n*c) in
    rewrite sym xy in
    rewrite add結合則 x (n*a) (n*c) in
    rewrite sym $ 分配則' n a c in
    Refl))


-- integer
data Z = Pos N | Neg N

negZeroIsZero : Neg O = Pos O
negZeroIsZero = believe_me "definition"

Oz : Z
Oz = Pos O

Iz : Z
Iz = Pos I

negate : Z -> Z
negate (Pos n) = Neg n
negate (Neg n) = Pos n

doubleNegElim : (z : Z) -> negate (negate z) = z
doubleNegElim (Pos n) = Refl
doubleNegElim (Neg n) = Refl

(-) : N -> N -> Z
(-) a O = Pos a
(-) O b = Neg b
(-) (S a) (S b) = (-) a b 

zeroMinusN : (n : N) -> O-n = Neg n
zeroMinusN O = rewrite negZeroIsZero in Refl
zeroMinusN (S n) = Refl

nMinusSelf : (n : N) -> n-n = Oz
nMinusSelf O = Refl
nMinusSelf (S n) = rewrite nMinusSelf n in Refl


minus交換したらnegate : (n, m : N) -> n-m = negate (m-n)
minus交換したらnegate O O = rewrite negZeroIsZero in Refl
minus交換したらnegate O (S m) = Refl
minus交換したらnegate (S n) O = Refl
minus交換したらnegate (S n) (S m) = minus交換したらnegate n m



zSucc : Z -> Z
zSucc (Pos n) = Pos (S n)
zSucc (Neg O) = Pos I
zSucc (Neg (S n)) = Neg n

zPred : Z -> Z
zPred (Neg n) = Neg (S n)
zPred (Pos O) = Neg I
zPred (Pos (S n)) = Pos n

zSuccPred : (a : Z) -> zSucc (zPred a) = a
zSuccPred (Pos O) = rewrite negZeroIsZero in Refl
zSuccPred (Neg O) = Refl
zSuccPred (Pos (S n)) = Refl
zSuccPred (Neg (S n)) = Refl

zPredSucc : (a : Z) -> zPred (zSucc a) = a
zPredSucc (Pos O) = Refl
zPredSucc (Neg O) = rewrite negZeroIsZero in Refl
zPredSucc (Pos (S n)) = Refl
zPredSucc (Neg (S n)) = Refl


posZadd : N -> Z -> Z
posZadd O b = b
posZadd (S n) b = zSucc $ posZadd n b

negZadd : N -> Z -> Z
negZadd O b = b
negZadd (S n) b = zPred $ negZadd n b

infixl 8 +.
(+.) : Z -> Z -> Z
(Pos n) +. b = posZadd n b
(Neg n) +. b = negZadd n b

zPplusP : (a, b : N) -> Pos a +. Pos b = Pos (a+b)
zPplusP O b = Refl
zPplusP (S a) b = rewrite zPplusP a b in Refl

zNplusN : (a, b : N) -> Neg a +. Neg b = Neg (a+b)
zNplusN O b = Refl
zNplusN (S a) b = rewrite zNplusN a b in Refl

zPplusN : (a, b : N) -> Pos a +. Neg b = a-b
zPplusN O b = rewrite zeroMinusN b in Refl
zPplusN (S a) b = rewrite zPplusN a b in rewrite f a b in Refl
  where
    f : (a, b : N) -> zSucc (a-b) = (S a - b)
    f O O = Refl
    f a O = Refl
    f (S a) (S b) = rewrite f a b in Refl

zNplusP : (a, b : N) -> Neg a +. Pos b = b-a
zNplusP O b = Refl
zNplusP (S a) b = rewrite zNplusP a b in rewrite f a b in Refl
  where
    f : (a, b : N) -> zPred (b-a) = (b - S a)
    f O O = Refl
    f a O = rewrite zeroMinusN a in Refl
    f (S a) (S b) = rewrite f a b in Refl

zPlusNegSelf : (a : Z) -> a +. negate a = Oz
zPlusNegSelf (Pos n) = rewrite zPplusN n n in rewrite nMinusSelf n in Refl
zPlusNegSelf (Neg n) = rewrite zNplusP n n in rewrite nMinusSelf n in Refl


zAdd交換則 : (a, b : Z) -> a +. b = b +. a
zAdd交換則 (Pos a) (Pos b) =
  rewrite zPplusP a b in
  rewrite zPplusP b a in
  rewrite add交換則 a b in Refl
zAdd交換則 (Neg a) (Neg b) =
  rewrite zNplusN a b in
  rewrite zNplusN b a in
  rewrite add交換則 a b in Refl
zAdd交換則 (Pos a) (Neg b) =
  rewrite zPplusN a b in rewrite zNplusP b a in Refl
zAdd交換則 (Neg a) (Pos b) =
  rewrite zPplusN b a in rewrite zNplusP a b in Refl

zAdd0 : (a : Z) -> a +. Oz = a
zAdd0 a = rewrite zAdd交換則 a Oz in Refl

zSuccAdd : (a, b : Z) -> zSucc a +. b = zSucc (a +. b)
zSuccAdd (Pos O) b = Refl
zSuccAdd (Pos (S an)) b = Refl
zSuccAdd (Neg O) b = Refl
zSuccAdd (Neg (S an)) b = rewrite zSuccPred (negZadd an b) in Refl

zPredAdd : (a, b : Z) -> zPred a +. b = zPred (a +. b)
zPredAdd (Pos O) b = Refl
zPredAdd (Pos (S an)) b = rewrite zPredSucc (posZadd an b) in Refl
zPredAdd (Neg O) b = Refl
zPredAdd (Neg (S an)) b = Refl


zAdd結合則 : (a, b, c : Z) -> (a +. b) +. c = a +. (b +. c)
zAdd結合則 = theorem where
  f : (n : N) -> (b, c : Z) -> ((Pos n) +. b) +. c = (Pos n) +. (b +. c)
  f O b c = Refl
  f (S n) b c =
    rewrite zSuccAdd (posZadd n b) c in
    rewrite f n b c in Refl

  g : (n : N) -> (b, c : Z) -> ((Neg n) +. b) +. c = (Neg n) +. (b +. c)
  g O b c = Refl
  g (S n) b c =
    rewrite zPredAdd (negZadd n b) c in
    rewrite g n b c in Refl

  theorem : (a, b, c : Z) -> (a +. b) +. c = a +. (b +. c)
  theorem (Pos an) b c = f an b c
  theorem (Neg an) b c = g an b c




posZmul : N -> Z -> Z
posZmul O b = Oz
posZmul (S n) b = b +. posZmul n b

negZmul : N -> Z -> Z
negZmul O b = Oz
negZmul (S n) b = (negate b) +. negZmul n b

infixl 9 *.
(*.) : Z -> Z -> Z
(Pos n) *. b = posZmul n b
(Neg n) *. b = negZmul n b


zPxP : (a, b : N) -> Pos a *. Pos b = Pos (a*b)
zPxP O b = Refl
zPxP (S a) b = rewrite zPxP a b in rewrite zPplusP b (a*b) in Refl

zPxN : (a, b : N) -> Pos a *. Neg b = Neg (a*b)
zPxN O b = rewrite negZeroIsZero in Refl
zPxN (S a) b = rewrite zPxN a b in rewrite zNplusN b (a*b) in Refl

zNxP : (a, b : N) -> Neg a *. Pos b = Neg (a*b)
zNxP O b = rewrite negZeroIsZero in Refl
zNxP (S a) b = rewrite zNxP a b in rewrite zNplusN b (a*b) in Refl

zNxN : (a, b : N) -> Neg a *. Neg b = Pos (a*b)
zNxN O b = Refl
zNxN (S a) b = rewrite zNxN a b in rewrite zPplusP b (a*b) in Refl

zMul交換則 : (a, b : Z) -> a *. b = b *. a
zMul交換則 (Pos a) (Pos b) =
  rewrite zPxP a b in
  rewrite zPxP b a in
  rewrite mul交換則 a b in Refl
zMul交換則 (Pos a) (Neg b) =
  rewrite zPxN a b in
  rewrite zNxP b a in
  rewrite mul交換則 a b in Refl
zMul交換則 (Neg a) (Pos b) =
  rewrite zPxN b a in
  rewrite zNxP a b in
  rewrite mul交換則 a b in Refl
zMul交換則 (Neg a) (Neg b) =
  rewrite zNxN a b in
  rewrite zNxN b a in
  rewrite mul交換則 a b in Refl

zX0 : (a : Z) -> a *. Oz = Oz
zX0 a = rewrite zMul交換則 a Oz in Refl

z1X : (a : Z) -> Iz *. a = a
z1X a = rewrite zAdd0 a in Refl

zX1 : (a : Z) -> a *. Iz = a
zX1 a = rewrite zMul交換則 a Iz in rewrite z1X a in Refl

negateIsMulNeg1 : (a : Z) -> negate a = a *. (Neg I)
negateIsMulNeg1 a =
  rewrite zMul交換則 a (Neg I) in
  rewrite zAdd交換則 (negate a) (Pos O) in Refl


zsuccmul : (a, b : Z) -> zSucc a *. b = b +. a *. b
zsuccmul (Pos n) b = Refl
zsuccmul (Neg O) b = Refl
zsuccmul (Neg (S n)) b =
  rewrite sym $ zAdd結合則 b (negate b) (negZmul n b) in
  rewrite zPlusNegSelf b in Refl


zMul結合則 : (a, b, c :Z) -> (a*.b)*.c = a*.(b*.c)
zMul結合則 (Pos a) (Pos b) (Pos c) =
  rewrite zPxP a b in
  rewrite zPxP b c in
  rewrite zPxP (a*b) c in
  rewrite zPxP a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Pos a) (Pos b) (Neg c) =
  rewrite zPxP a b in
  rewrite zPxN b c in
  rewrite zPxN (a*b) c in
  rewrite zPxN a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Pos a) (Neg b) (Pos c) =
  rewrite zPxN a b in
  rewrite zNxP b c in
  rewrite zNxP (a*b) c in
  rewrite zPxN a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Pos a) (Neg b) (Neg c) =
  rewrite zPxN a b in
  rewrite zNxN b c in
  rewrite zNxN (a*b) c in
  rewrite zPxP a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Neg a) (Pos b) (Pos c) =
  rewrite zNxP a b in
  rewrite zPxP b c in
  rewrite zNxP (a*b) c in
  rewrite zNxP a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Neg a) (Pos b) (Neg c) =
  rewrite zNxP a b in
  rewrite zPxN b c in
  rewrite zNxN (a*b) c in
  rewrite zNxN a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Neg a) (Neg b) (Pos c) =
  rewrite zNxN a b in
  rewrite zNxP b c in
  rewrite zPxP (a*b) c in
  rewrite zNxN a (b*c) in
  rewrite mul結合則 a b c in Refl
zMul結合則 (Neg a) (Neg b) (Neg c) =
  rewrite zNxN a b in
  rewrite zNxN b c in
  rewrite zPxN (a*b) c in
  rewrite zNxP a (b*c) in
  rewrite mul結合則 a b c in Refl

negateMul : (a, b : Z) -> negate (a*.b) = negate a *. b
negateMul (Pos a) (Pos b) = rewrite zPxP a b in rewrite zNxP a b in Refl
negateMul (Pos a) (Neg b) = rewrite zPxN a b in rewrite zNxN a b in Refl
negateMul (Neg a) (Pos b) = rewrite zNxP a b in rewrite zPxP a b in Refl
negateMul (Neg a) (Neg b) = rewrite zNxN a b in rewrite zPxN a b in Refl

negateAdd : (a, b : Z) -> negate (a+.b) = negate a +. negate b
negateAdd (Pos a) (Pos b) =
  rewrite zPplusP a b in rewrite zNplusN a b in Refl
negateAdd (Pos a) (Neg b) =
  rewrite zPplusN a b in rewrite zNplusP a b in
  rewrite minus交換したらnegate b a in Refl
negateAdd (Neg a) (Pos b) =
  rewrite zNplusP a b in rewrite zPplusN a b in
  rewrite minus交換したらnegate a b in Refl
negateAdd (Neg a) (Neg b) =
  rewrite zNplusN a b in rewrite zPplusP a b in Refl


z分配則 : (a, b, c : Z) -> a *. (b+.c) = a*.b +. a*.c
z分配則 = theorem where
  fp : (n : N) -> (b, c : Z) -> (Pos n)*.(b+.c) = (Pos n)*.b+.(Pos n)*.c 
  fp O b c = Refl
  fp (S an) b c =
    let a = Pos an in
    rewrite zAdd結合則 b (a*.b) (c+.a*.c) in
    rewrite zAdd結合則 b c (a*.(b+.c)) in
    rewrite zAdd交換則 (a*.b) (c+.a*.c) in
    rewrite zAdd結合則 c (a*.c) (a*.b) in
    rewrite zAdd交換則 b c in
    rewrite fp an c b in
    Refl

  fn : (n : N) -> (b, c : Z) -> (Neg n)*.(b+.c) = (Neg n)*.b+.(Neg n)*.c 
  fn an b c =
    let a = Pos an in
    rewrite sym $ negateMul a (b +. c) in
    rewrite fp an b c in
    rewrite negateAdd (a*.b) (a*.c) in
    rewrite negateMul a b in
    rewrite negateMul a c in
    Refl

  theorem : (a, b, c : Z) -> a *. (b+.c) = a*.b +. a*.c 
  theorem (Pos an) b c = fp an b c
  theorem (Neg an) b c = fn an b c



main : IO ()
main = do
  putStrLn $ "Q.E.D."
