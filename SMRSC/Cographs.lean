--
-- SMRSC.Cographs
--

--
-- "Infinite" trees/graphs
--

import Batteries
import Aesop

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc

--
-- Lazy cographs of configurations
--

-- A `LazyGraph8 α` represents a (potentially) infinite set of graphs
-- of configurations (whose type is `Graph α`).
--
-- "Lazy" cographs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyCoraph

inductive LazyGraph8Node (α : Type) (G : Type) : Type where
  | empty8 : LazyGraph8Node α G
  | stop8  : (c : α) -> LazyGraph8Node α G
  | build8 : (c : α) ->
      (lss : List (List G)) ->
      LazyGraph8Node α G

class LazyGraph8  (α : Type) (G : Type) : Type where
  get : G -> LazyGraph8Node α G

structure GenG α : Type where
  s : ScWorld α
  h : List α
  c : α


-- BigStepMRSC8

-- build_graph8

namespace GenG

mutual

def get_g {α} (g : GenG α) : LazyGraph8Node α (GenG α)
:=
  match g.s.foldableToHistory? g.c g.h with
  | .isTrue _ => .stop8 g.c
  | .isFalse _ =>
      .build8 g.c (get_css g (g.s.develop g.c))

def get_css {α} (g : GenG α) :
      (css : List (List α)) -> List (List (GenG α))
  | [] => []
  | cs :: css =>
      get_cs g cs :: get_css g css

def get_cs {α} (g : GenG α) :
      (cs : List α) -> List (GenG α)
  | [] => []
  | c :: cs =>
      ⟨g.s, (g.c :: g.h), c⟩ :: get_cs g cs

end

end GenG

def build_graph8 {α} (s : ScWorld α) (c : α) : GenG α
  := ⟨s, [], c⟩

instance {α} : LazyGraph8 α (GenG α) where
  get := GenG.get_g

-- prune_graph8

def prune_graph8_l {α G} [l : LazyGraph8 α G] (w : BarWhistle α)
    (h : List α) (b : Bar w.dangerous h) (g : G) :
    LazyGraph α
:=
  match l.get g with
  | .empty8 => .empty
  | .stop8 c => .stop c
  | .build8 c lss => match w.dangerous? h with
      | isTrue _ => .empty
      | isFalse nd => match b with
          | .now d => False.elim (nd d)
          | .later bs =>
              .build c (lss.map (List.map (prune_graph8_l w (c :: h) (bs c))))

def prune_graph8 {α G} [l : LazyGraph8 α G] (w : BarWhistle α) (l : G) :
      LazyGraph α
:= prune_graph8_l w [] w.barNil l

--
-- Now that we have docomposed `lazy_mrsc`
--     lazy_mrsc ≗ prune_cograph ∘ build_cograph
-- we can push some cleaners into prune_cograph.
--
-- Suppose `clean∞` is a cograph cleaner such that
--     clean ∘ prune_cograph ≗ prune_cograph ∘ clean∞
-- then
--     clean ∘ lazy_mrsc ≗
--       clean ∘ (prune_cograph ∘ build_cograph) ≗
--       (prune_cograph ∘ clean∞) ∘ build_cograph
--       prune_cograph ∘ (clean∞ ∘ build_cograph)
--
-- The good thing is that `build_cograph` and `clean∞` work in a lazy way,
-- generating subtrees by demand. Hence, evaluating
--     ⟪ prune_cograph ∘ (clean∞ (build_cograph c))  ⟫
-- may be less time and space consuming than evaluating
--     ⟪ clean (lazy_mrsc c) ⟫
--

-- cl8_bad_conf

structure Cl8Bad α G [LazyGraph8 α G] where
  bad : α -> Bool
  g : G

namespace Cl8Bad

def get_l {α G} (bad : α -> Bool) [LazyGraph8 α G] (g : G) :
    LazyGraph8Node α (Cl8Bad α G)
:=
  match LazyGraph8.get g with
  | .empty8 =>
      .empty8
  | .stop8 c =>
      if bad c then .empty8 else .stop8 c
  | .build8 c lss =>
      if bad c then
        .empty8
      else
        .build8 c (lss.map (List.map (fun l => ⟨bad, l⟩)))

end Cl8Bad

instance {α G} [LazyGraph8 α G] : LazyGraph8 α (Cl8Bad α G) where
  get bg := Cl8Bad.get_l bg.bad bg.g

def cl8_bad_conf {α G} [LazyGraph8 α G] (bad : α -> Bool) (g : G) : Cl8Bad α G
  := ⟨bad, g⟩

--
-- A cograph can be cleaned to remove some empty alternatives.
--
-- Note that the cleaning is not perfect, because `cl8_empty` has to pass
-- the productivity check.
-- So, `build c []` is not (recursively) replaced with `Ø`. as is done
-- by `cl-empty`.
--

def empty8? {α G} [l : LazyGraph8 α G] (g : G) : Bool
:=
  match l.get g with
  | .empty8 => true
  | .stop8 _ => false
  | .build8 _ _ => false

-- cl8_empty

structure Cl8Empty α G [LazyGraph8 α G] where
  g : G

namespace Cl8Empty

mutual

def get_l {α G} [LazyGraph8 α G] (g : G) : LazyGraph8Node α (Cl8Empty α G)
:=
  match LazyGraph8.get g with
  | .empty8 => .empty8
  | .stop8 c => .stop8 c
  | .build8 c lss =>
      .build8 c (get_lss lss)

def get_lss {α G} [l : LazyGraph8 α G] : (lss : List (List G)) ->
      List (List (Cl8Empty α G))
  | [] => []
  | ls :: lss =>
      if ls.any (@empty8? α G l) then
        get_lss lss
      else
        ls.map (fun g => ⟨g⟩) :: get_lss lss

end

end Cl8Empty

instance {α G} [LazyGraph8 α G] : LazyGraph8 α (Cl8Empty α G) where
  get x := Cl8Empty.get_l x.g

def cl8_empty {α G} [LazyGraph8 α G] (g : G) : Cl8Empty α G
  := ⟨g⟩


-- An optimized version of `prune_cograph`.
-- The difference is that empty subtrees are removed
-- "on the fly".

-- prune0_graph8

mutual

partial
def prune0_graph8_l {α G} [l : LazyGraph8 α G] (w : BarWhistle α)
    (h : List α) (b : Bar w.dangerous h) (g : G) :
    LazyGraph α
:=
  match l.get g with
  | .empty8 => .empty
  | .stop8 c => .stop c
  | .build8 c lss => match w.dangerous? h with
      | isTrue _ => .empty
      | isFalse nd => match b with
          | .now d => False.elim (nd d)
          | .later bs =>
              cl_empty_build c (prune0_graph8_lss w (c :: h) (bs c) lss)

partial
def prune0_graph8_lss {α G} [l : LazyGraph8 α G] (w : BarWhistle α)
    (h : List α) (b : Bar w.dangerous h) : (lss : List (List G)) ->
    List (List (LazyGraph α))
  | [] => []
  | ls :: lss => match prune0_graph8_ls w h b ls with
      | none => prune0_graph8_lss w h b lss
      | some ls' => ls' :: prune0_graph8_lss w h b lss

partial
def prune0_graph8_ls {α G} [LazyGraph8 α G] (w : BarWhistle α)
    (h : List α) (b : Bar w.dangerous h) : (ls : List G) ->
    Option (List (LazyGraph α))
  | [] => some []
  | l :: ls =>
      let l' := prune0_graph8_l w h b l
      if @empty8? α G _ l then
        none
      else
        match prune0_graph8_ls w h b ls with
        | none => none
        | some ls' => some (l' :: ls')

end

def prune0_graph8 {α G} [LazyGraph8 α G] (w : BarWhistle α)
      (g : G) : LazyGraph α
:= prune0_graph8_l w [] w.barNil g
