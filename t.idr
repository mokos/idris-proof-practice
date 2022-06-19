%default total -- 証明を網羅しないと怒られる設定にする

-- 自然数の型 N を再帰的に定義する
data N = O | S N  -- S は、後続数（successor）の意

I   : N           -- Iは自然数
I   = S O         -- IはOの次の数
II  : N           -- IIは自然数
II  = S (S O)     -- IIは0の次の次の数
III : N
III = S (S (S O))
IV  : N
IV  = S (S (S (S O)))
V   : N
V   = S (S (S (S (S O))))


-- たし算の定義
-- a + b
(+) : N -> N -> N      -- Nを2つ引数にとってNを返すという関数の型
O     + b = b          -- aがゼロの場合
(S k) + b = k + (S b)  -- aが非ゼロ(S k)の場合、Sを右の引数側に寄せる

-- はじめての証明
add_3_2_is_5 : III + II = V
add_3_2_is_5 = Refl -- Idris処理系が勝手に計算してくれて、自動で証明完了




-- 任意の自然数のaとbについて「a+(bの次の数) = (a+b)の次の数」が成り立つ
-- （bの次の数）を足すことは、bを足してから次の数を見るのと同じ。
addSucc : (a : N) -> (b : N) -> a + (S b) = S (a+b)

-- a=0のときは、両辺が(S b)になるのでただちに証明完了
addSucc O     b = Refl

-- a=kで成り立つとして、a=(S k)でも成り立つことを示す（数学的帰納法）
addSucc (S k) b = 
                             --↓ (S k)+(S b) = S(S k + b) を得たい。
                             --↓ (+)関数の規則(Sの右寄せ)が勝手に自動適用される
                             --↓ k + (S (S b)) = S(k + S b)
  rewrite addSucc k (S b) in --↓ S(k+S b) = S(k+S b) ←addSucc規則(a=k)で置き換え
  Refl                       -- 得たい式を変形すると、常に成り立つReflだった(証明終)

-- 任意の自然数aに0を足しても変わらない
add0 : (a : N) -> a + O = a
add0 O     = Refl
add0 (S k) = rewrite addSucc k O in rewrite add0 k in Refl






add交換則 : (a : N) -> (b : N) -> a+b = b+a
-- a=0のときは、0+b = b+0 で、右辺をadd0規則でbに置き換えるだけ
add交換則 O     b = rewrite add0 b in Refl

-- a=kで成り立つとして、a=(S k)でも成り立つことを示す（数学的帰納法）
add交換則 (S k) b =        --↓ (S k) + b = b + (S k) を得たい。
                           --↓ (+)関数の規則(Sの右寄せ)が勝手に自動適用される
                           --↓ k+(S b) = b+(S k) 
  rewrite addSucc   k b in --↓ S(k+b) = b+(S k) ←左辺に addSucc 規則を適用
  rewrite addSucc   b k in --↓ S(k+b) = S(b+k) ←右辺に addSucc 規則を適用
  rewrite add交換則 k b in --↓ S(b+k) = S(b+k) ←左辺に add交換則(a=k)を適用
  Refl                     -- 得たい式を変形すると、常に成り立つReflだった(証明終)


main : IO ()
main = do
  putStrLn $ "Q.E.D."
