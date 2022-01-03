%hide reverse

%default total

appendNil : (x : List a) -> x ++ [] = x
appendNil [] = Refl
appendNil (x::xs) = rewrite appendNil xs in Refl

append結合則 : (x, y, z : List a) -> (x ++ y) ++ z = x ++ (y ++ z)
append結合則 []      y z = Refl
append結合則 (x::xs) y z = rewrite append結合則 xs y z in Refl

reverse : List a -> List a
reverse [] = []
reverse (x::xs) = (reverse xs) ++ [x]

reverseOfAppend : (xs, ys : List a) ->
    reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseOfAppend [] ys = rewrite appendNil (reverse ys) in Refl
reverseOfAppend (x::xs) ys =
  rewrite reverseOfAppend xs ys in
  rewrite append結合則 (reverse ys) (reverse xs) [x] in
  Refl

reverseのreverseは元通り : (xs : List a) -> reverse (reverse xs) = xs
reverseのreverseは元通り [] = Refl
reverseのreverseは元通り (x::xs) =
  rewrite reverseOfAppend (reverse xs) [x] in
  rewrite reverseのreverseは元通り xs in
  Refl

main : IO ()
main =
  do
    print a
    print $ reverse a
    print $ reverse $ reverse a
  where
    a : List Int
    a = [1, 3, 5]
