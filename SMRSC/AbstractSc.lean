--
-- SMRSC.AbstractSc
--

import Batteries
import Aesop

/- ### Schemes of different types of supercompilation ### -/

/-
As presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164.
-/

/-
### Notation: ###

  g – a current graph of configurations
  β – a current node in a graph of configurations
  c – a configuration in a current node β
-/

class ScWorld where
  Graph : Type
  Configuration : Type
  Node : Type
  DriveInfo : Type

  conf : Node -> Configuration

  Foldable : (g : Graph) -> (b a : Node) -> Prop
  foldable : (g : Graph) -> (b : Node) -> Option Node
  fold : (g : Graph) -> (b a : Node) -> Graph

  driveStep : Configuration -> DriveInfo
  addChildren : (g : Graph) -> (b : Node) -> (cs : DriveInfo) -> Graph

  rebuilding : (c : Configuration) -> Configuration
  InRebuildings : (c' c : Configuration) -> Prop
  rebuild : (g : Graph) -> (b : Node) -> (c' : Configuration) -> Graph

  dangerous : (g : Graph) -> (b : Node) -> Bool

  foldable_correct {g a b} :
    foldable g b = some a -> Foldable g b a
  rebuilding_correct {c c'} :
    rebuilding c = c' -> InRebuildings c' c

open ScWorld

/-
### (a) SC: Deterministic (traditional) supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  dangerous(g, β)
  c′ = rebuilding(g, c)
  ----------------------
  g → rebuild(g, β, c′)
-/

inductive SC [ScWorld] : (g g' : Graph) -> Prop where
  | fold {g a b} :
      (f : foldable g b = some a) ->
        SC g (fold g b a)
  | drive {g b cs} :
      (not_f : foldable g b = none) ->
      (not_w : dangerous g b = false) ->
      (d : driveStep (conf b) = cs) ->
        SC g (addChildren g b cs)
  | rebuild {g b c c'} :
      (not_f : foldable g b = none) ->
      (w : dangerous g b = true) ->
      (r : rebuilding c = c') ->
        SC g (rebuild g b c')

/-
### (b) NDSC: Non-deterministic supercompilation (transformation relation) ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  ----------------------
  g → rebuild(g, β, c′)

-/

inductive NDSC [ScWorld] : (g g' : Graph) -> Prop where
  | fold {g b a} :
      (f : foldable g b = some a) ->
        NDSC g (fold g b a)
  | drive {g b cs} :
      (not_f : foldable g b = none) ->
      (d : driveStep (conf b) = cs) ->
        NDSC g (addChildren g b cs)
  | rebuild {g b c c'} :
      (not_f : foldable g b = none) ->
      (rs : InRebuildings c' c) ->
        NDSC g (rebuild g b c')

/-
### (c) MRSC: Multi-result supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  -----------------------------------------
  g → rebuild(g, β, c′)

-/

inductive MRSC [ScWorld] : (g g' : Graph) -> Prop where
  | fold {g b a} :
      (f : foldable g b = some a) ->
        MRSC g (fold g b a)
  | drive {g b cs} :
      (not_f : foldable g b = none) ->
      (not_w : dangerous g b = false) ->
      (d : driveStep (conf b) = cs) ->
        MRSC g (addChildren g b cs)
  | rebuild {g b c c'} :
      (not_f : foldable g b = none) ->
      (rs : InRebuildings c' c) ->
        MRSC g (rebuild g b c')


-- Now let us prove some "natural" theorems.
-- A formal verification is useful
-- just to ensure that "the ends meet".

-- This model of supercompilation is extremely abstract.
-- So there is not much to prove.

theorem SC_MRSC [ScWorld] {g g'} : SC g g' -> MRSC g g'
  | .fold f =>
      .fold f
  | .drive not_f not_w d =>
      .drive not_f not_w d
  | .rebuild not_f _ r =>
      .rebuild not_f (rebuilding_correct r)

theorem MRSC_NDSC [ScWorld] {g g'} : MRSC g g' -> NDSC g g'
  | .fold f =>
      .fold f
  | .drive not_f _ d =>
      .drive not_f d
  | .rebuild not_f rs =>
      .rebuild not_f rs

theorem SC_NDSC [ScWorld] {g g'} : SC g g' -> NDSC g g'
  | .fold f =>
      .fold f
  | .drive not_f _ d =>
      .drive not_f d
  | .rebuild not_f _ r =>
      .rebuild not_f (rebuilding_correct r)

-- Transitive closures

inductive Star {a} (r : a -> a -> Prop) : a -> a -> Prop where
  | nil {x} : Star r x x
  | cons {x y z} : r x y -> Star r y z -> Star r x z

notation " [] " => Star.nil
infixr:67 " :: " => Star.cons

def Star.append {a} {x y z : a} {r} : Star r x y -> Star r y z -> Star r x z := fun
  | .nil, s2 => s2
  | .cons h s1, s2 => h :: (.append s1 s2)

infixl:65 " ++ "  => Star.append

def StarSC [ScWorld] : Graph -> Graph -> Prop :=
  Star SC

def StarNDSC [ScWorld] : Graph -> Graph -> Prop :=
  Star NDSC

def StarMRSC [ScWorld] : Graph -> Graph -> Prop :=
  Star MRSC

-- Theorems

def StarSC_StarMRSC [ScWorld] {g g'} : StarSC g g' -> StarMRSC g g'
  | [] => []
  | h :: s => SC_MRSC h :: StarSC_StarMRSC s

def StarMRSC_StarNDSC [ScWorld] {g g'} : StarMRSC g g' -> StarNDSC g g'
  | [] => []
  | h :: s => MRSC_NDSC h :: StarMRSC_StarNDSC s

def StarSC_StarNDSC [ScWorld] {g g'} : StarSC g g' -> StarNDSC g g'
  := StarMRSC_StarNDSC ∘ StarSC_StarMRSC
