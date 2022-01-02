%hide reverse
%hide reverseOnto

%default total

reverseOnto : List a -> List a -> List a
reverseOnto acc [] = acc
reverseOnto acc (x::xs) = reverseOnto (x::acc) xs

reverse : List a -> List a
reverse xs = reverseOnto [] xs

reverse_reverse : List a -> List a
reverse_reverse x = reverse $ reverse x



a : List Int
a = [1, 3, 5]

main : IO ()
main = do
  print a
  print $ reverse a
  print $ reverse_reverse a
  where
    b : Int
    b = 3
