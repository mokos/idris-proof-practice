%default total

ならば推移律 : (p -> q, q -> r) -> (p -> r)
ならば推移律 (hpq, hqr) = hqr . hpq

モーダスポーネンス : (p -> q, p) -> q
モーダスポーネンス (hpq, hp) = hpq hp 

main : IO ()
main = do
  putStr "Q.E.D."
