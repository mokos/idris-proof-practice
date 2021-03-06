%default total

-- ビルトインの機能は使う
-- - Pair型
-- - (=) 関係 (=, sym, rewrite, replace)
-- - Not 関係 (Not, Void, void)
-- - 依存型 (x : TYpe ** P a)
-- それ以外(Preludeにあるもの)は基本自前で定義していく。


-- 命題の同値演算子
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


-- 不等号
(/=) : a -> a -> Type
x /= y = Not (x=y)

不等号の対称律 : a /= b -> b /= a
不等号の対称律 abn ba = abn $ sym ba


-- 自然数
--- (S (S n)) を S S n と書けるようにする
prefix 99 `S`

--- ペアノの公理
-- 1. ゼロは自然数
-- 2. すべての自然数には次の数（successor : 後続数）があり、それも自然数

data N = O | S N

--- ペアノの公理 3. 0は後続数ではない
zeroIsNotSucc : {n : N} -> O /= S n
zeroIsNotSucc Refl impossible -- Nの定義からOが後続数になり得ないことを証明できる

succIsNotZero : {n : N} -> S n /= O
succIsNotZero = 不等号の対称律 zeroIsNotSucc

--- ペアノの公理 4. succの単射性
違うならsuccも違う : {m, n : N} -> m/=n -> S m/=S n
違うならsuccも違う = believe_me "axiom" -- 公理として定義

-- 標準ライブラリのcongと同等
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

_1x : (n : N) -> I * n = n
_1x O = Refl
_1x (S n) = rewrite _1x n in Refl

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



-- 不等号
-- lt  : <  less than
-- lte : <= less than equal
-- gt  : >  greater than
-- gte : >= greater than equal

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

gtImplyGt2 : {m, n : N} -> m>n -> m>.n
gtImplyGt2 = ltImplyLt2

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

lt推移律 : {x, y, z: N} -> (x<y, y<z) -> x<z
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

lteOrGt : (m, n : N) -> (m<=n) || (m>n)
lteOrGt m n with (eqOrIneq m n)
  | L eq = L (R eq)
  | R (L lt) = L (L lt)
  | R (R gt) = R gt

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

lteImplyNgt : {m, n : N} -> m<=n -> Not(m>n)
lteImplyNgt (L lt) = ltImplyNgt lt 
lteImplyNgt (R eq) = eqImplyNgt eq

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
正整数を足すと大きくなる _ O {nz} impossible
正整数を足すと大きくなる n (S d) = lt2ImplyLt (d ** Refl)

ltAddNat : {m, n : N} -> m<n -> (k : N) -> m+k<n+k
ltAddNat {m}{n} lt O = rewrite add0 n in rewrite add0 m in lt
ltAddNat {m=O}{n=S c} Lt0 (S a) =
  rewrite add交換則 (S c) (S a) in 正整数を足すと大きくなる (S a) (S c)
ltAddNat (LtSucc x) k = LtSucc $ ltAddNat x k

ltMulPos : {m, n : N} -> m<n -> (k : N) -> {auto nz : k>O} -> m*k<n*k
ltMulPos {nz} _ O impossible
ltMulPos {n=O} lt (S a) = void $ notLt0 lt
ltMulPos {m=O}{n=S c} lt (S a) = Lt0
ltMulPos {m=S b}{n=S c} (LtSucc x) k =
  rewrite add交換則 k (c*k) in
  rewrite add交換則 k (b*k) in
  ltAddNat (ltMulPos {m=b}{n=c} x k) k

ltMulNat : {m, n : N} -> m<n -> (k : N) -> m*k<=n*k
ltMulNat {m}{n} _ O = R $ rewrite x0 n in rewrite sym $ x0 m in Refl
ltMulNat {m}{n} lt (S k) = L $ ltMulPos lt (S k)

lteMulNat : {m, n : N} -> m<=n -> (k : N) -> m*k<=n*k
lteMulNat (R eq) k = R $ rewrite eq in Refl
lteMulNat (L lt) k = ltMulNat lt k

lteMulNat' : {m, n : N} -> m<=n -> (k : N) -> k*m<=k*n
lteMulNat' {m}{n} lte k = rewrite mul交換則 k m in rewrite mul交換則 k n in lteMulNat lte k

大きい方に足しても大きい : {m, n : N} -> m<n -> (k : N) -> m<n+k
大きい方に足しても大きい Lt0 k = Lt0
大きい方に足しても大きい (LtSucc x) k = LtSucc $ 大きい方に足しても大きい x k

大きい方に正整数をかけても大きい : {m, n : N} -> m<n -> (p : N) -> {auto nz : p>O} -> m<n*p
大きい方に正整数をかけても大きい _ O impossible
大きい方に正整数をかけても大きい {n} lt (S p) = 
  rewrite xSucc n p in 大きい方に足しても大きい lt (n*p)

正整数に2以上をかけると大きくなる : (m, n : N) -> {auto c : (m>O, n>I)} -> m<m*n
正整数に2以上をかけると大きくなる m n {c=(m1, n2)} =
  rewrite mul交換則 m n in
  rewrite sym $ _1x m in
  rewrite sym $ mul結合則 n (S O) m in
  rewrite x1 n in
  ltMulPos n2 m

正整数に2以上をかけると2以上 : (m, n : N) -> {auto c : (m>O, n>I)} -> I < m*n
正整数に2以上をかけると2以上 O n {c=(m1, _)} impossible
正整数に2以上をかけると2以上 (S O) n = 正整数に2以上をかけると大きくなる (S O) n 
正整数に2以上をかけると2以上 (S S m) n =
  lt推移律 ((LtSucc Lt0), (正整数に2以上をかけると大きくなる (S S m) n))

正整数をかけると減らない : {n, p : N} -> {auto nz : p>O} -> n<=n*p
正整数をかけると減らない {p=O} impossible
正整数をかけると減らない {n=O} = R $ Refl
正整数をかけると減らない {n}{p=S O} = R $ rewrite x1 n in Refl
正整数をかけると減らない {n=S a}{p=S S b} = L $ 正整数に2以上をかけると大きくなる (S a) (S S b)

足しても同じなら足した数は0 : {a, d : N} -> a+d=a -> d=O
足しても同じなら足した数は0 {d=O} eq = Refl
足しても同じなら足した数は0 {a}{d=S dd} eq = void $ notLtSelf {n=a} $ lt2ImplyLt (dd ** eq)

同じものを足して同じなら同じ : {a, b, d : N} -> a+d=b+d -> a=b
同じものを足して同じなら同じ {a}{b}{d=O} eq = rewrite sym (add0 a) in rewrite sym (add0 b) in eq
同じものを足して同じなら同じ {a}{b}{d=S dd} eq =
  同じものを足して同じなら同じ {a}{b}{d=dd} eq_prev 
    where
      eq_prev : a+dd=b+dd
      eq_prev = succが同じなら同じ $ rewrite sym (addSucc a dd) in replace (addSucc b dd) eq

同じものに足して同じなら同じ : {a, b, d : N} -> d+a=d+b -> a=b
同じものに足して同じなら同じ {a}{b}{d} eq =
  同じものを足して同じなら同じ {a}{b}{d} $ rewrite (add交換則 a d) in replace (add交換則 d b) eq


-- d |. n とは、 dがnを割り切ること（nはdの倍数）
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
  正整数を割り切れるのはそれ以下の正整数 {d=k}{k=d} (rewrite mul交換則 k d in ndk)


-- 素数
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
    | O impossible
    | S O = L (Refl, ltImplyNeq $ LtSucc Lt0)
    | (S S a)
      with (lt)
      | (LtSucc (LtSucc x)) = void $ notLt0 x


互いに素 : (x, y : N) -> Type
互いに素 x y = {d : N} -> (d |. x, d |. y) -> d=I


-- ユークリッドやサイダックの素数の無限性の証明に必要な性質

naとnb十1が同じならnは1 : {n, a, b : N} -> n*a = n*b+I -> n=I
naとnb十1が同じならnは1 {n=O}    {a}{b} eq = eq
naとnb十1が同じならnは1 {n=S O}  {a}{b} eq = Refl
naとnb十1が同じならnは1 {n=S S k}{a}{b} eq =
  -- 矛盾型(Void)が返ってきたとき、void関数によりどんな結論も導ける
  void $ nが2以上のとき矛盾 (S S k) a b eq
    where
      nが2以上のとき矛盾 : (n, a, b : N) -> {auto c : n>I} -> n*a = n*b+I -> Void
      nが2以上のとき矛盾 n a b eq with (lteOrGt a b)
       | L a_lte_b   = lteImplyNgt (lteMulNat' a_lte_b n) $ lt2ImplyLt (O ** sym eq)
       | R a_gt__b with (gtImplyGt2 a_gt__b)
         | (d ** f) = notLtSelf i_lt_i
           where
             f1 : a=b+S d
             f1 = sym f
             -- na=nb+1 に eq1 を代入
             f2 : n*(b+(S d))=n*b+I
             f2 = rewrite sym f1 in eq
             -- 左辺を展開
             f3 : n*b+n*(S d)=n*b+I 
             f3 = rewrite sym (分配則' n b (S d)) in f2
             -- 両辺のnbを取り除く
             f4 : n*(S d)=I
             f4 = 同じものに足して同じなら同じ f3
             -- n>=2、S d>=1なので、積は2以上になるが、右辺は1なので矛盾する
             f5 : n*(S d)>I
             f5 = rewrite mul交換則 n (S d) in 正整数に2以上をかけると2以上 (S d) n
             i_lt_i : I<I
             i_lt_i = replace f4 f5


nが2以上ならna十1はnで割り切れない :
  {n, a : N} -> {auto nは2以上 : n>I} -> (n |. n*a+I) -> Void
nが2以上ならna十1はnで割り切れない {n}{a}{nは2以上} div with (div)
  -- f = n*a+I=d*n
  | (d ** f) = notLtSelf i_lt_i
    where
      nは1 : n=I
      nは1 = naとnb十1が同じならnは1 $ sym f

      i_lt_i : I<I
      i_lt_i = replace nは1 nは2以上


-- set
単射 : (t -> u) -> Type
単射 f {t} = (x, y : t) -> (f x = f y) -> (x = y) 

-- ref. https://gist.github.com/cheery/696db4cd50370e19adaa77909eb6f908#file-finitesets-idr-L51

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

重複がない : List n -> Type
重複がない xs = 単射 $ indexer xs


main : IO ()
main = do
  putStrLn $ "Q.E.D."
