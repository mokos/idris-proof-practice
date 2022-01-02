%default total

--data 同値関係 : (P, Q : Type) -> (A : (p->q, q->p)) -> Type where
  --Douti : 同値関係 p q (p->q, q->p)

Douti : (p, q : Type) -> { same : (p->q, q->p) } -> Type
Douti p q {same} = p

g : (p : Type) -> Type
g p = Douti p p { same = (id, id) }

or交換 : Either a b -> Either b a
or交換 (Left  a) = Right a
or交換 (Right b) = Left  b

and交換 : (a, b) -> (b, a)
and交換 (a, b) = (b, a)


同語反復 : {P : Type} -> P -> P
同語反復 p = p

三段論法 : {P, Q : Type} -> ((P -> Q), P) -> Q
三段論法 (pq, p) = pq p

真ならば : {P, Q : Type} -> P -> (Q -> P)
真ならば p _ = p

偽ならば : {P, Q : Type} -> Not P -> (P -> Q)
偽ならば np p = void (np p)

ならば否定 : {P, Q : Type} -> ((P -> Q), Not Q) -> Not P
ならば否定 (pq, nq) p = nq (pq p)

ならば分岐 : (a->b, a->c) -> (a->(b, c))
ならば分岐 (ab, ac) a = (ab a, ac a)

ならば選択 : Either (a->b) (a->c) -> a -> Either b c
ならば選択 (Left  ab) a = Left  (ab a)
ならば選択 (Right ac) a = Right (ac a)

同じ結論 : (a->c, b->c) -> (Either a b -> c)
同じ結論 (ac, bc) (Left  a) = ac a
同じ結論 (ac, bc) (Right b) = bc b

いずれにせよ論法 : (Either a b, a->c, b->c) -> c
いずれにせよ論法 (ab, ac, bc) = 同じ結論 (ac, bc) ab

どちらかの前提から結論 : Either (a->c) (b->c) -> ((a, b) -> c)
どちらかの前提から結論 (Left  ac) (a, _) = ac a
どちらかの前提から結論 (Right bc) (_, b) = bc b

二重否定 : {P : Type} -> P -> (Not (Not P))
二重否定 p np = np p

三重否定除去 : {P : Type} -> Not (Not (Not P)) -> Not P
三重否定除去 nnnp p = nnnp (二重否定 p)

対偶 : (a->b) -> (Not b -> Not a)
対偶 hab nb a = nb (hab a)

ならばをnandに : (a->b) -> Not (a, Not b)
ならばをnandに ab (a, nb) = nb (ab a)

--ならばをORにするのは排中律に等しい

andをならばに : (a, Not b) -> Not (a->b)
andをならばに (a, nb) ab = nb (ab a)

orをならばに : Either (Not a) b -> (a->b)
orをならばに (Left na) a = void (na a)
orをならばに (Right b) a = b

or消去法 : (Either a b, Not a) -> b
or消去法 (Left a, na) = void (na a)
or消去法 (Right b, _) = b

真かつ偽は矛盾 : {P : Type} -> (P, Not P) -> Void
真かつ偽は矛盾 (hp, hnp) = hnp hp

肯定ならば否定は否定 : (p -> Not p) -> Not p
肯定ならば否定は否定 pnp p =
  真かつ偽は矛盾 ((ならば分岐 (同語反復, pnp)) p)

否定ならば肯定は二重否定 : (Not p -> p) -> Not (Not p)
否定ならば肯定は二重否定 npp np = np (npp np)

ドモルガンnor : Not (Either p q) -> ((Not p), (Not q))
ドモルガンnor hnpq =
  let np = hnpq . Left  in
  let nq = hnpq . Right in
  (np, nq)

排中律の二重否定 : {P : Type} -> Not (Not (Either P (Not P)))
排中律の二重否定 h = 真かつ偽は矛盾 $ ドモルガンnor h

排中律 : Type
排中律 = {P : Type} -> Either P (Not P)

排中律' : Type
排中律' = ((P : Type) -> Either P (Not P))

二重否定除去 : Type
二重否定除去 = {P : Type} -> Not (Not P) -> P

二重否定除去を仮定すると排中律 : 二重否定除去 -> 排中律
二重否定除去を仮定すると排中律 h = h 排中律の二重否定

ならばをor表現できると排中律 :
  ({a, b : Type} -> (a->b) -> Either b (Not a)) -> 排中律
ならばをor表現できると排中律 h = h 同語反復 

パースの法則を仮定すると二重否定除去 : 
  ({a, b : Type} -> ((a -> b) -> a) -> a) -> 二重否定除去
パースの法則を仮定すると二重否定除去 h nnp = h (void . nnp)

-- ちょっとずるい。普通のNANDだとどうやるのか
ドモルガン亜種を仮定すると排中律 :
  ({a, b : Type} -> Not (Not a, Not b) -> Either a b) -> 排中律
ドモルガン亜種を仮定すると排中律 h = h 真かつ偽は矛盾

-- {a : Type} にすると謎のエラー
排中律を仮定すると二重否定除去 :
  排中律' -> {P : Type} -> Not (Not P) -> P
排中律を仮定すると二重否定除去 h {P=P} nnp
  with (h P)
    | Left  p  = p
    | Right np = void (nnp np)

排中律を仮定するとならばをor表現 :
  排中律' -> {P, Q : Type} -> (P -> Q) -> Either Q (Not P)
排中律を仮定するとならばをor表現 h {P=P} pq
  with (h P)
    | Left  p  = Left (pq p)
    | Right np = Right np

--pqp Not (pq, Not b)
排中律を仮定するとパース :
  排中律' -> {p, q : Type} -> ((p -> q) -> p) -> p
排中律を仮定するとパース h {p=p} pqp
  with (h p)
    | Left  pp = pp
    | Right np = pqp (偽ならば np)

排中律を仮定するとダメット :
  排中律' -> {p, q : Type} -> Either (p->q) (q->p)
排中律を仮定するとダメット h {p=p}
  with (h p)
    | Left pp = Right $ 真ならば pp
    | Right np = Left $ 偽ならば np


------------- ドモルガン論理 ----------------
弱排中律 : Type
弱排中律 = {P : Type} -> Either (Not (Not P)) (Not P)

ドモルガン : Type
ドモルガン = {P, Q : Type} -> Not (P, Q) -> Either (Not P) (Not Q)

ドモルガンを仮定すると弱排中律 : ドモルガン -> 弱排中律
ドモルガンを仮定すると弱排中律 h = or交換 $ h 真かつ偽は矛盾

nandをならばに : Not (p, q) -> (p -> Not q)
nandをならばに nab p q = nab (p, q)

弱排中律を仮定するとドモルガンnand :
  ((a : Type) -> Either (Not (Not a)) (Not a)) ->
   {p, q : Type} -> Not (p, q) -> Either (Not p) (Not q)
弱排中律を仮定するとドモルガンnand h {p=p}{q=q} npq
  with (h p)
    | Right np = Left np
    | Left nnp with (h q)
      | Right nq = Right nq
      | Left nnq = Left ((対偶 (nandをならばに npq)) nnq)

弱排中律から排中律が導けるならそもそも二重否定除去できる :
  ((A, B : Type) ->
    Either (Not (Not A)) (Not A) ->
    Either B (Not B)
  ) -> {P : Type} -> Not (Not P) -> P
弱排中律から排中律が導けるならそもそも二重否定除去できる h {P=P} nnp
  with ((h P P) (Left nnp))
    | Left p = p
    | Right np = void (nnp np)

demorgan1 : ((Not p), (Not q)) -> Not (Either p q)
demorgan1 (hnp, _) (Left  p) = hnp p
demorgan1 (_, hnq) (Right q) = hnq q


demorgan2 : Either (Not p) (Not q) -> Not (p, q)
demorgan2 (Left  hp) (p, q) = hp p
demorgan2 (Right hq) (p, q) = hq q

demorgan4 : Either a b -> Not (Not a, Not b)
demorgan4 (Left  a) (na, _) = na a
demorgan4 (Right b) (_, nb) = nb b

demorgan5 : (a, b) -> Not (Either (Not a) (Not b))
demorgan5 (a, b) (Left  na) = na a
demorgan5 (a, b) (Right nb) = nb b

-------------- ゲーデル論理 ------------------
-- https://www.asianprofile.wiki/wiki/Intermediate_logic
-- ダメット法則は、ならばで命題の全順序がつけられるということ
-- 比較可能で、推移律と反対称律が成り立つ
-- 排中律を仮定するとダメット成り立つので、古典論理に含まれる
ダメットの法則を仮定すると弱排中律 :
  ({a, b : Type} -> Either (a->b) (b->a)) ->
   {P : Type} -> Either (Not (Not P)) (Not P)
ダメットの法則を仮定すると弱排中律 h {P=P}
  with (h {a=P}{b=Not P})
    | Left  pnp = Right $ 肯定ならば否定は否定     pnp
    | Right npp = Left  $ 否定ならば肯定は二重否定 npp



main : IO ()
main = do
  putStr "Q.E.D."
