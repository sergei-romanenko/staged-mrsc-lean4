--
-- SMRSC.AlmostFullRel
--

import Batteries
import Aesop

--
-- Almost-full relations
--

inductive AlmostFull {α : Type} : (r : α -> α -> Prop) -> Type where
  | now   {r} : ((x y : α) -> r x y) ->
      AlmostFull r
  | later {r} : ((u : α) -> AlmostFull (fun x y => r x y ∨ r u x)) ->
      AlmostFull r

-- af_mono

def af_mono {α p q} (pq : {x y : α} -> p x y -> q x y) :
      AlmostFull p -> AlmostFull q
  | .now h => .now fun x y => pq (h x y)
  | .later h =>
      AlmostFull.later fun u =>
      have : ∀ {x y : α}, p x y ∨ p u x → q x y ∨ q u x :=
        (Or.elim · (Or.inl ∘ pq) (Or.inr ∘ pq))
      af_mono this (h u)

--
-- Well-founded trees
--

inductive WFT : (α  :  Type) -> Type where
  | now {α}   : WFT α
  | later {α} : (s : α -> WFT α) -> WFT α

--
-- The tree can be separated from the relation.
--
-- (This is a form of "staging", a wft being a "program" that
-- transforms a relation.)

-- SecureBy r t

def SecureBy {α} (r : α -> α -> Prop) : (t :  WFT α) -> Prop := fun
  | .now => ∀ x y, r x y
  | .later s =>
      ∀ u, SecureBy (fun x y => r x y ∨ r u x) (s u)

-- AlmostFullT

def AlmostFullT {α} (r : α -> α -> Prop) :=
  {p // SecureBy r p}

-- aft_to_af

def aft_to_af' {α} {r : α -> α -> Prop} : (t : WFT α) -> (s : SecureBy r t) -> AlmostFull r
  | .now, s => .now s
  | .later l, s => .later fun u =>
      aft_to_af' (l u) (s u)

def aft_to_af {α} {r : α -> α -> Prop} : AlmostFullT r -> AlmostFull r
  | ⟨t, s⟩ => aft_to_af' t s


-- af_to_aft

def af_to_aft {α : Type} {r : α -> α -> Prop} : AlmostFull r -> AlmostFullT r
  | .now h => ⟨.now, h⟩
  | .later h =>
      have step := fun u => af_to_aft (h u)
      ⟨ .later fun u => (step u).val, fun u => (step u).property ⟩


-- Given `AlmostFull r`, we can extract the corresponding wft tree.

-- af_to_wft

def wft {α : Type} {r : α -> α -> Prop} : AlmostFull r -> WFT α := fun
  | .now _ => .now
  | .later s => .later fun u => wft (s u)

-- af_to_wft is sound.

-- af_to_sb

def af_to_sb {α : Type} {r : α -> α -> Prop} :
      (af : AlmostFull r) -> SecureBy r (wft af)
  | .now z => z
  | .later s => fun u => af_to_sb (s u)

--
-- In some proofs there appear expressons of the form
--     f (af_mono p⇒q (s c))
-- so that the termination checker cannot see that the argument of f
-- is smaller than `(later s)` . But the function f is total, because
-- `wft (s c)` is smaller than `wft (s c)` and
--      wft (af_mono p⇒q (s c)) ≡ wft (s c)
-- This is made explicit in the signature of sb_mono ,
-- so that we can use induction on t, rather than on `AlmostFull r` .

-- sb_mono

def sb_mono {α : Type} {p q : α -> α -> Prop}
  (t : WFT α) (sp : SecureBy p t) (pq: ∀ x y, p x y → q x y) :
      SecureBy q t :=
  match t with
  | .now => fun x y => pq x y (sp x y)
  | .later s =>
      fun u =>
      show SecureBy (fun x y => q x y ∨ q u x) (s u) from
      sb_mono (s u) (sp u) (fun x y =>
        show p x y ∨ p u x → q x y ∨ q u x from
        (Or.elim · (Or.inl ∘ pq x y) (Or.inr ∘ pq u x)))
