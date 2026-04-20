--
-- SMRSC.BarWhistles
--

import Batteries
import Aesop

/-
In our model of big-step supercompilation whistles are assumed to be
"inductive bars". See:

Thierry Coquand. About Brouwer's fan theorem. September 23, 2003.
Revue internationale de philosophie, 2004/4 n° 230, p. 483-489.

http://www.cairn.info/revue-internationale-de-philosophie-2004-4-page-483.htm
http://www.cairn.info/load_pdf.php?ID_ARTICLE=RIP_230_0483
-/

import SMRSC.Util
import SMRSC.AlmostFullRel

-- Bar

-- The set of finite paths such that either
-- (1) d h is valid right now; or
-- (2) for all possible a1 :: h either
--     (1) d (a1 :: h) is valid right now; or
--     (2) for all possible a2 :: a1 :: h either ...

inductive Bar {α : Type} (d : List α -> Prop) :
         (h : List α) -> Type where
  | now   {h} : (dh : d h) -> Bar d h
  | later {h} : (bs : ∀ c, Bar d (c :: h)) -> Bar d h

structure BarWhistle α where
  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  -- Dangerous histories
  dangerous {α} : (h : List α) -> Prop
  dangerous? : (h : List α) -> Decidable (dangerous h)

  -- Bar-induction
  -- (In Coquand's terms, `Bar dangerous` is required to be "an inductive bar".)

  barNil : Bar dangerous []

-- BarGen

-- This namespace shows the generation of finite sequences
-- by means of a BarWhistle α.

namespace BarGen

variable {α : Type} (w : BarWhistle α) (step : List α -> α)
open BarWhistle

def barGen' (h : List α) : (b : Bar w.dangerous h) ->
      {h' : List α // w.dangerous h'}
  | .now dh => ⟨h, dh⟩
  | .later bs =>
      have c : α := step h
      barGen' (c :: h) (bs c)

def barGen : {h : List α // w.dangerous h}
  := barGen' w step [] w.barNil

end BarGen

-- A fan, or an finitely branching tree, is a tree
-- each node of which has a finite number of immediate successor nodes.

inductive Fan (α : Type) : Type where
  | fan : List (α × Fan α) -> Fan α

-- BarFanGen

-- This namespace shows the generation of finitely branching trees
-- by means of a bar whistle.

namespace BarFanGen

variable {α : Type} (w : BarWhistle α) (step : List α -> List α)
open BarWhistle

def fanGen' (h : List α) : (b : Bar w.dangerous h) -> Fan α := fun
  | .now _ =>
      .fan []
  | .later bs =>
      .fan ((step h).map (fun c => (c , fanGen' (c :: h) (bs c))))

end BarFanGen

--
-- Bar d h is "monotonic" with respect to d.
--

-- bar_mono

def bar_mono {α} {d d' : List α -> Prop}
  (mono : (h : List α) -> d h -> d' h) (h : List α) :
      (b : Bar d h) -> Bar d' h
  | .now d_h =>
      .now $ mono h d_h
  | .later bs =>
      .later (fun c => bar_mono mono (c :: h) (bs c))

-- bar_or

def bar_or {α} {d d' : List α -> Prop} (h : List α)
      (b : Bar d h) : Bar (fun h => d h ∨ d' h) h
  := bar_mono (fun _ dh' => Or.inl dh') h b

--
-- Bar whistles based on the length of the sequence
--

-- pathLengthWhistle

instance pathLengthWhistle (α : Type) (l : Nat) : BarWhistle α :=
  let dangerous (h : List α) : Prop
    := l ≤  h.length
  let dangerous? (h : List α) : Decidable (dangerous h)
    := l.decLe h.length

  let bar (m : Nat) (h : List α) (d : m + h.length = l) : Bar dangerous h
    := by
    induction m generalizing h with
    | zero =>
        apply Bar.now
        subst d
        simp_all only [Nat.zero_add, ge_iff_le, Nat.le_refl, dangerous]
    | succ m' ih =>
        apply Bar.later
        intro c
        subst d
        simp_all only [dangerous]
        apply ih
        grind only [= List.length_cons]

  let barNil : Bar dangerous []
    := bar l [] (Nat.add_eq_left.mpr rfl)

  ⟨dangerous, dangerous?, barNil⟩

--
-- WFT, SecureHBy, BarT
--

/-
inductive WFT : (α  :  Type) -> Type where
  | now {α}   : WFT α
  | later {α} : (s : α -> WFT α) -> WFT α
 -/

def SecureHBy {α} (d : List α -> Prop) : (h : List α) -> (t :  WFT α) -> Prop
  | h, .now => d h
  | h, .later s =>
      ∀ c, SecureHBy d (c :: h) (s c)

def BarT {α : Type} (d : List α -> Prop) (h : List α) :=
  {t // SecureHBy d h t}

--
-- Bar d h <--> BarT d h
--

def bart_to_bar' {α} (d : List α -> Prop) (h : List α) :
      (t : WFT α) -> (s : SecureHBy d h t) -> Bar d h
  | .now, s => .now s
  | .later l, s => .later fun c => bart_to_bar' d (c :: h) (l c) (s c)

def bart_to_bar {α} (d : List α -> Prop) (h : List α) : BarT d h -> Bar d h
  | ⟨t, s⟩ => bart_to_bar' d h t s

def bar_to_bart {α} (d : List α -> Prop) (h : List α) : (b : Bar d h) -> BarT d h
  | .now dh => ⟨.now, dh⟩
  | .later bs =>
      let h := fun c => bar_to_bart d (c :: h) (bs c)
      ⟨.later fun c => (h c).val, fun c => (h c).property⟩

--
-- BarWhistleT α
--

class BarWhistleT α where
  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  -- Dangerous histories
  dangerous {α} : (h : List α) -> Prop
  dangerous? : (h : List α) -> Decidable (dangerous h)

  -- Bar-induction
  -- (In Coquand's terms, `BarT dangerous` is required to be "an inductive bar".)

  barNil : BarT dangerous []

--
-- BarWhistle α <--> BarWhistleT α
--

def bw_to_bwt {α} (w : BarWhistle α) : BarWhistleT α
  := ⟨w.dangerous, w.dangerous?,
      bar_to_bart w.dangerous [] w.barNil⟩

def bwt_to_bw {α} (w : BarWhistleT α) : BarWhistle α
  := ⟨w.dangerous, w.dangerous?,
      bart_to_bar w.dangerous [] w.barNil⟩


-- BarGen

-- This namespace shows the generation of finite sequences
-- by means of a BarWhistle α.

namespace BarGenT

variable {α : Type} [w : BarWhistleT α] (step : List α -> α)
open BarWhistleT

def barGenT' (h : List α) : (t : WFT α) -> (s : SecureHBy dangerous h t)  ->
      {h' : List α // dangerous h'}
  | .now, dh => ⟨h, dh⟩
  | .later l, s =>
      have c : α := step h
      barGenT' (c :: h) (l c) (s c)

def barGenT : {h : List α // dangerous h}
  := barGenT' step [] barNil.val barNil.property

end BarGenT

--
-- Bar whistles based on inverse image
--

-- inverseImageWhistleT

instance inverseImageWhistleT {α β : Type} (f : α -> β)
    (w : BarWhistleT β) : BarWhistleT α
  :=

  let dangerous := w.dangerous ∘ List.map f
  let dangerous? := fun h => w.dangerous? (List.map f h)

  let rec bar : (h : List α) -> (t : WFT β) -> (s : SecureHBy w.dangerous (List.map f h) t) ->
            BarT dangerous h :=
        fun h => fun
          | .now, dh => ⟨.now, dh⟩
          | .later l, s =>
              have h := fun c => bar (c :: h) (l (f c)) (s (f c))
              ⟨.later fun c => (h c).val, fun c => (h c).property⟩

  let barNil : BarT dangerous [] := bar [] w.barNil.val w.barNil.property

  ⟨ dangerous, dangerous?, barNil ⟩

-- inverseImageWhistle

instance inverseImageWhistle {α β : Type} (f : α -> β) :
    (w : BarWhistle β) -> BarWhistle α
  :=
  ( · |> bw_to_bwt |> inverseImageWhistleT f |> bwt_to_bw)

--
-- Bar whistles based on well-founded relations
--

inductive AccT {α : Type} (r : α -> α -> Prop) : α -> Type where
  | intro (x : α) (h : (y : α) -> r y x -> AccT r y) : AccT r x

inductive WellFoundedT {α : Type} (r : α → α → Prop) : Type where
  | intro (h : (a : α) -> AccT r a) : WellFoundedT r

def WellFoundedT.apply {α : Type} {r : α → α → Prop} :
          (wf : WellFoundedT r) -> (a : α) -> AccT r a
    | .intro h => h

-- wfWhistle

namespace WFWhistle

variable {α} (r : α -> α -> Prop)

def dangerous : (h : List α) -> Prop
  | [] => False
  | (_ :: []) => False
  | (c' :: c :: h) => (¬ r c' c) ∨ (dangerous (c :: h))

variable [DecidableRel r]

def dangerous? : (h : List α) -> Decidable (dangerous r h)
  | [] => isFalse id
  | _ :: [] => isFalse id
  | c' :: c :: h =>
      match dangerous? (c :: h) with
      | isFalse ndch =>
          if h : r c' c then
            isFalse (fun | .inl nrc'c => nrc'c h | .inr dch => ndch dch)
          else
            isTrue (.inl h)
      | isTrue dch => isTrue (.inr dch)

def bar (c : α) (h : List α) :
      AccT r c -> Bar (dangerous r) (c :: h)
  | ⟨c, rs⟩ =>
      match dangerous? r (c :: h) with
      | isTrue dch => .now dch
      | isFalse _ => .later $ fun c' =>
          if rc'c : r c' c then
            bar c' (c :: h) (rs c' rc'c)
          else
            .now (.inl rc'c)

def barNil (wf : WellFoundedT r) : Bar (dangerous r) [] :=
  .later  fun c => bar r c [] (wf.apply c)

def barT (c : α) (h : List α) :
      AccT r c -> BarT (dangerous r) (c :: h)
  | ⟨c, rs⟩ =>
      match dangerous? r (c :: h) with
      | isTrue dch => ⟨.now, dch⟩
      | isFalse _ =>
          let h := fun c' =>
            if rc'c : r c' c then
              barT c' (c :: h) (rs c' rc'c)
            else
              ⟨.now, .inl rc'c⟩
          ⟨.later fun c => (h c).val, fun c => (h c).property⟩

def barNilT (wf : WellFoundedT r) : BarT (dangerous r) []
  :=
  let h := fun c => barT r c [] (wf.apply c)
  ⟨.later fun c => (h c).val, fun c => (h c).property⟩

end WFWhistle

instance wfWhistle {α : Type} (r : α -> α -> Prop) (dr : DecidableRel r)
                    (wf : WellFoundedT r) : BarWhistle α
  := ⟨ WFWhistle.dangerous r, WFWhistle.dangerous? r, WFWhistle.barNil r wf ⟩

instance wfWhistleT {α : Type} (r : α -> α -> Prop) (dr : DecidableRel r)
                    (wf : WellFoundedT r) : BarWhistleT α
  := ⟨ WFWhistle.dangerous r, WFWhistle.dangerous? r, WFWhistle.barNilT r wf ⟩

--
-- Whistles based on the idea that some elements of the sequence
-- "cover" other elements.
-- (covers c' c) means that c' "covers" c.
--

namespace CWhistle

variable {α : Type} (covers : α -> α -> Prop)

def h_covers : (h : List α) -> (c : α) -> Prop
  | [], _ => False
  | c' :: h, c => covers c' c ∨ h_covers h c

def dangerous : (h : List α) -> Prop
  | [] => False
  | c :: h => h_covers covers h c ∨ dangerous h

variable (covers? : DecidableRel covers)

def h_covers? : (h : List α) -> (c : α) -> Decidable (h_covers covers h c)
  | [], _ => isFalse id
  | c' :: h, c =>
      match covers? c' c with
      | isFalse ncc'c =>
          match h_covers? h c with
          | isFalse nhc => isFalse (Or.elim · ncc'c nhc)
          | isTrue hc => isTrue (.inr hc)
      | isTrue cc'c => isTrue (.inl cc'c)

def dangerous? : (h : List α) -> Decidable (dangerous covers h)
  | [] => isFalse id
  | c :: h =>
      match h_covers? covers covers? h c with
      | isFalse nhc =>
          match dangerous? h with
          | isFalse nhdh => isFalse (Or.elim · nhc nhdh)
          | isTrue hdh => isTrue (.inr hdh)
      | isTrue hc => isTrue (.inl hc)

end CWhistle

-- CWhistle

instance CWhistle {α : Type} (covers : α -> α -> Prop) (covers? : DecidableRel covers)
          (c_barNil : Bar (CWhistle.dangerous covers) [])
      : BarWhistle α
  := ⟨ CWhistle.dangerous covers,
        -- fun _ _ => .inr,
        CWhistle.dangerous? covers covers?,
        c_barNil ⟩

class CWorld {α : Type} where
  covers : α -> α -> Prop
  covers? : DecidableRel covers

--
-- Almost-full relations
--

namespace BarC_AfC

variable {α : Type} (covers : α -> α -> Prop) (covers? : DecidableRel covers)

open CWhistle (dangerous h_covers)

def r_h_covers (h : List α) (x y : α) : Prop
  := dangerous covers (x :: h) ∨ (covers x y)

-- barc_to_afc

def barc_to_afc (h : List α) :
      Bar (dangerous covers) h -> AlmostFull (r_h_covers covers h)
  | .now dh =>
      .now fun _ _ => .inl (.inr dh)
  | .later bs =>
      let afch (c : α) : AlmostFull (r_h_covers covers (c :: h))
            := barc_to_afc (c :: h) (bs c)
      let step (c : α) {x} {y} : r_h_covers covers (c :: h) x y ->
              (r_h_covers covers h x y) ∨ (r_h_covers covers h c x)
        := calc
            r_h_covers covers (c :: h) x y
        _ ⇒ dangerous covers (x :: c :: h) ∨ covers x y
              := id
        _ ⇒ ((h_covers covers (c :: h) x ∨ dangerous covers (c :: h)) ∨ covers x y)
              := id
        _ = (((covers c x ∨ h_covers covers h x) ∨
              (h_covers covers h c ∨ dangerous covers h)) ∨ covers x y)
              := rfl
        _ ⇒ (((h_covers covers h x ∨ dangerous covers h) ∨ covers x y) ∨
               ((h_covers covers h c ∨ dangerous covers h) ∨ covers c x))
              := (Or.elim ·
                    (Or.elim ·
                      (Or.elim · (.inr ∘ .inr) (.inl ∘ .inl ∘ .inl))
                      (Or.elim · (.inr ∘ .inl ∘ .inl) (.inl ∘ .inl ∘ .inr)))
                    (.inl ∘ .inr))
        _ = ((dangerous covers (x :: h) ∨ covers x y) ∨ (dangerous covers (c :: h) ∨ covers c x))
              := rfl
        _ = ((r_h_covers covers h x y) ∨ (r_h_covers covers h c x))
              := rfl

      .later fun c => af_mono (step c) (afch c)

-- aftc_to_barc

def aftc_to_barc (h : List α) :
      (t : WFT α) -> SecureBy (r_h_covers covers h) t -> Bar (dangerous covers) h
  | .now, s =>
      let help (c' c : α) : dangerous covers (c :: h) ∨ covers c c' ->
            dangerous covers (c' :: c :: h)
          := calc
              dangerous covers (c :: h) ∨ covers c c'
          _ ⇒ ((covers c c' ∨ (h_covers covers h c')) ∨ dangerous covers (c :: h))
                := (Or.elim · .inr (.inl ∘ .inl))
          _ = (h_covers covers (c :: h) c' ∨ dangerous covers (c :: h))
                := rfl
          _ = dangerous covers (c' :: c :: h)
                := rfl

      .later (fun c => .later (fun c' => .now (help c' c (s c c'))))
  | .later l, s =>
      let step (c : α) (x y : α) : r_h_covers covers h x y ∨ r_h_covers covers h c x ->
            r_h_covers covers (c :: h) x y
        := calc
            (r_h_covers covers h x y ∨ r_h_covers covers h c x)
        _ = ((dangerous covers (x :: h) ∨ covers x y) ∨ dangerous covers (c :: h) ∨ covers c x)
              := rfl
        _ = (((h_covers covers h x ∨ dangerous covers h) ∨ covers x y) ∨
                  (h_covers covers h c ∨ dangerous covers h) ∨ covers c x)
              := rfl
        _ ⇒ ((h_covers covers (c :: h) x ∨ dangerous covers (c :: h)) ∨ covers x y)
              := (Or.elim ·
                    (Or.elim · (Or.elim · (.inl ∘ .inl ∘ .inr) (.inl ∘ .inr ∘ .inr)) .inr)
                    (Or.elim · (Or.elim · (.inl ∘ .inr ∘ .inl) (.inl ∘ .inr ∘ .inr))
                                (.inl ∘ .inl ∘ .inl)))
        _ = (dangerous covers (x :: c :: h) ∨ covers x y)
              := rfl
        _ = r_h_covers covers (c :: h) x y
              := rfl
      let help (c : α) : Bar (dangerous covers) (c :: h) :=
        aftc_to_barc (c :: h) (l c) (sb_mono (l c) (s c) (step c))
      .later (fun c => help c)

-- afc_to_barc

def afc_to_barc (h : List α) (af : AlmostFull (r_h_covers covers h)) : Bar (dangerous covers) h
  :=
  let ⟨t, s⟩ := af_to_aft af
  aftc_to_barc covers h t s

--
-- barc <-> afc
--

-- This doesn't work, because Bar and AlmostFull are Type-s, rather than Prop-s

-- def barc_iff_afc (h : List α) :
--   Bar (dangerous covers) h <-> AlmostFull (r_h_covers covers h)
--   := Iff.intro (barc_to_afc h) (afc_to_barc h)

end BarC_AfC
