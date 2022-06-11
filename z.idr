-- 一旦別ファイルに移動
-- このままでは動かない

-- 法として合同
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

