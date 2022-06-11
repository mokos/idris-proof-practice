import Data.Fin
%default total

単射 : (t -> u) -> Type
単射 f {t} = (x, y : t) -> (f x = f y) -> (x = y) 

f : Fin 3 -> Nat
f FZ = 1
f (FS FZ) = 1
f (FS (FS FZ)) = 1

fは単射 : 単射 Main.f
fは単射 FZ FZ eq = Refl  
fは単射 FZ (FS FZ) eq = Refl  

main : IO ()
main = do
  putStr "Q.E.D."
