import Data.Fin
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

--Iを割り切れるのはIのみ : {k : N} -> k |. I -> k=I
--Iを割り切れるのはIのみ {k} (d ** eq)
--  with (正整数を割り切れるのはそれ以下の正整数 eq)
--  | (nz, L lt1) = ?h
--  | (_,  R eq1) = eq1

isPrime : (x : N) -> Type
isPrime x = (d : N) -> (d |. x) -> xor (d=I) (d=x)

_0は素数ではない : Not (isPrime O)
_0は素数ではない f with (f (S S O) (ゼロは自然数で割り切れる (S S O)))
  | L (eq, neq) = 違うならsuccも違う succIsNotZero $ eq
  | R (eq, neq) = succIsNotZero eq

_1は素数ではない : Not (isPrime I) 
_1は素数ではない f with (f I (正整数は1で割り切れる I))
  | L (eq, neq) = neq eq
  | R (eq, neq) = neq eq

_2は素数 : isPrime (S S O)
_2は素数 y (z ** f)
  with (正整数を割り切れるのはそれ以下の正整数' f)
  | (yp, R eq) = R (eq, rewrite eq in gtImplyNeq $ LtSucc Lt0)
  | (yp, L lt) 
    with (y)
    | O = void $ notLt0 yp
    | S O = L (Refl, ltImplyNeq $ LtSucc Lt0)
    | (S S a)
      with (lt)
      | (LtSucc (LtSucc x)) = void $ notLt0 x


互いに素 : (x, y : N) -> Type
互いに素 x y = {d : N} -> (x |. d, y |. d) -> d=I

-- Saidak による素数の無限性の証明
--差が1だと互いに素 : (x, y : N) -> (x+I=y) -> 互いに素 x y
--差が1だと互いに素 O y eq = ?h
  

-- ユークリッドの補題
--f : (p : N) -> {c : prime p} -> (a*b) |. p -> a |. p || b |. p

-- set
単射 : (t -> u) -> Type
単射 f {t} = (x, y : t) -> (f x = f y) -> (x = y) 

f : Fin 2 -> N
f FZ = O 
f (FS FZ) = S O

fは単射 : 単射 Main.f
fは単射 FZ FZ eq = Refl  
fは単射 FZ (FS FZ) eq = void $ (ltImplyNeq Lt0) eq
fは単射 (FS FZ) (FS FZ) eq = Refl
fは単射 (FS FZ) FZ eq = void $ (gtImplyNeq Lt0) eq

data Nth : (xs : List a) -> Type where
  XZ : Nth (x :: xs)
  XS : Nth xs -> Nth (x :: xs)

indexer : (xs : List a) -> Nth xs -> a
indexer (x :: xs) XZ = x
indexer (x :: xs) (XS y) = indexer xs y

-- 有限個の自然数のリスト
data Ns : (len : N) -> Type where
  Nil : Ns O
  (::) : (x : N) -> (xs : Ns len) -> Ns (S len)

--len : {n : N} -> FinNats n -> N
--len {n} xs = n

重複がない : List n -> Type
重複がない xs = 単射 $ indexer xs

全部素数 : (t -> u) -> Type
全部素数 f {t} = (x : t) -> isPrime (f x)

素数リストにない素数を作れる : List N -> (p : N ** (isPrime(p)))
--m <. n = (d : N ** m + S d = n)

main : IO ()
main = do
  putStrLn $ "Q.E.D."
