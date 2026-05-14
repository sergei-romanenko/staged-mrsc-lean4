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
-- Agda-style "inspection"
--

def app_eq {α β} (f : α -> β) (x : α) : {y // f x = y}
:=
  let y := f x
  have h : f x = y := rfl
  ⟨y, h⟩

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

--
-- Some "technical" theorems about cartesian products
--

-- cartesian2_nil

theorem rw_cartesian2_nil {α} : (xs : List α) ->
  cartesian2 xs [] = []
  | [] => rfl
  | x :: xs => by
      rw [cartesian2, List.map_nil, List.nil_append]
      exact rw_cartesian2_nil xs

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

namespace List

def any_p {α} (p : α -> Prop) : List α -> Prop
  | [] => False
  | x :: xs => p x ∨ any_p p xs

def any_p? {α} (p : α -> Prop) [p? : DecidablePred p] : DecidablePred (any_p p)
  | [] => isFalse id
  | x :: xs => match p? x with
      | isTrue px => isTrue $ Or.inl px
      | isFalse npx => match any_p? p xs with
          | isTrue pxs => isTrue $ Or.inr pxs
          | isFalse npxs => isFalse $ fun pxxs => match pxxs with
              | .inl px => npx px
              | .inr pxs => npxs pxs

end List
