--
-- SMRSC.Util
--

import Batteries
import Aesop

--
-- Implication reasoning
--

-- Reasoning by implication
-- Implication is a preorder relation...

def «⇒» (p q : Prop) : Prop :=
  p -> q

instance impTrans : Trans «⇒» «⇒» «⇒» where
  trans pq qr := qr ∘ pq

infixr:20 " ⇒ " => «⇒»

--
-- Cartesian product
--

-- cartesian

def cartesian2 {α} : List α -> List (List α) -> List (List α)
  | [], _ => []
  | x :: xs, yss => List.map (x :: ·) yss ++ cartesian2 xs yss

def cartesian {α} : List (List α) -> List (List α)
  | [] => [ [] ]
  | xs :: xss => cartesian2 xs (cartesian xss)


/-
--
-- `Pointwise r xs ys` means that `r x y` for all respective
-- `xs.contains x` and `ys.contains y`.
--

inductive Pointwise {α β} (r : α -> β -> Type) : List α -> List β -> Prop where
  | nil  : Pointwise r [] []
  | cons {x y xs ys} :
      r x y -> Pointwise r xs ys -> Pointwise r (x :: xs) (y :: ys)
 -/

