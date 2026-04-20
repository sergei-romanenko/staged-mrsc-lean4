--
-- SMRSC.BigStepSc
--

/- ### Schemes of different types of big-step supercompilation ### -/

/-
A variation of the scheme presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164.
-/

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs

-- Now we formulate an idealized model of big-step multi-result
-- supercompilation.

-- The knowledge about the input language a supercompiler deals with
-- is represented by a "world of supercompilation", which is a record
-- that specifies the following.
--
-- * `α` is the type of "configurations". Note that configurations are
--   not required to be just expressions with free variables! In general,
--   they may represent sets of states in any form/language and as well may
--   contain any _additional_ information.
--
-- * `Foldable` is a "foldability relation". c << c' means that c is foldable to c'.
--   (In such cases c' is usually said to be " more general than c".)
--
-- * `foldable?` is a decision procedure for `Foldable`. This procedure is necessary
--   for implementing supercompilation in functional form.
--
-- * `develop` is a function that gives a number of possible decompositions of
--   a configuration. Let `c` be a configuration and `cs` a list of
--   configurations such that `c ∈ cs`. Then `c` can be "reduced to"
--   (or "decomposed into") configurations in `cs`.
--
--   Suppose that driving is determinstic and, given a configuration `c`,
--   produces a list of configurations `drive c`. Suppose that rebuilding
--   (generalization, application of lemmas) is non-deterministic and
--   `rebuildings c` is the list of configurations that can be produced by
--   rebuilding. Then (in this special case) `develop` is implemented
--   as follows:
--
--       develop c = [ drive c ] ++ map (:: []) (rebuildings c)
--
-- * `whistle` is a "bar whistle" that is used to ensure termination of
--   functional supercompilation (see the module `BarWhistles`).
--
-- * `History` is a list of configurations that have been produced
--   in order to reach the current configuration.
--
-- * `FoldableToHistory c h` means that `c` is foldable to a configuration in
--   the history `h`.
--
-- * `foldableToHistory? c h` decides whether `FoldableToHistory c h c h`.

-- ScWorld

structure ScWorld α where
  FoldableTo : (c c' : α) -> Prop
  foldableTo? : (c c' : α) -> Decidable (FoldableTo c c')
  develop : (c : α) -> List (List α)

def ScWorld.FoldableToHistory {α} (s : ScWorld α) (c : α) : (h : List α) -> Prop
  | [] => False
  | c' :: h => s.FoldableTo c c' ∨ FoldableToHistory s c h

def ScWorld.foldableToHistory? {α} (s : ScWorld α) (c : α) :
      (h : List α) -> Decidable (s.FoldableToHistory c h)
  | [] => isFalse id
  | c' :: h =>
      match s.foldableTo? c c' with
      | isTrue fcc' =>  isTrue (.inl fcc')
      | isFalse nfcc' =>
          match s.foldableToHistory? c h with
          | isTrue fch => isTrue (.inr fch)
          | isFalse nfch => isFalse (Or.elim · nfcc' nfch)


  -- If we need labeled edges in the graph of configurations,
  -- the labels can be hidden inside configurations.
  -- ("Configurations" do not have to be just symbolic expressions, as
  -- they can contain any additional information.)

structure ScWorldWithLabels β α where
  -- w : BarWhistle α
  Foldable : (c c' : α) -> Prop
  foldable? : (c c' : α) -> Decidable (Foldable c c')
  develop : (c : α) -> List (List (β × α))

-- injectLabelsInScWorld

-- def barWhistleWithLabels (w : BarWhistle α) : BarWhistle (β, α)

def barWhistleWithLabels {α β} (w : BarWhistle α) : BarWhistle (β × α)
  := @inverseImageWhistle (β × α) α (·.snd) w

def injectLabelsInScWorld {β α} (wl : ScWorldWithLabels β α) : ScWorld (β × α)
  :=
  let Foldable (c c' : β × α) : Prop :=
        wl.Foldable c.snd c'.snd
  let foldable? (c c' : β × α) : Decidable (wl.Foldable c.snd c'.snd) :=
        wl.foldable? c.snd c'.snd
  let develop (c : β × α) : List (List (β × α)) :=
        wl.develop c.snd
  ⟨Foldable, foldable?, develop⟩

--
-- Big-step non-deterministic supercompilation
--

mutual

@[aesop unsafe [constructors, cases]]
inductive NDSC {α} [BEq α] {s : ScWorld α} :
      (h : List α) -> (c : α) -> (g : Graph α) -> Prop where
  | fold {h c} :
      (f : s.FoldableToHistory c h) ->
        NDSC h c (.back c)
  | build {h c cs gs} :
      (nf : ¬s.FoldableToHistory c h) ->
      (i : cs ∈ s.develop c) ->
      (pw : NDSC_PW (c :: h) cs gs) ->
        NDSC h c (.forth c gs)

@[aesop unsafe [constructors, cases]]
inductive NDSC_PW {α} [BEq α] {s : ScWorld α} :
      (h : List α) -> (cs : List α) -> (gs : List (Graph α)) -> Prop where
  | nil {h} : NDSC_PW h [] []
  | cons {h c g cs gs} :
      (p : NDSC h c g) -> (pw : NDSC_PW h cs gs) ->
        NDSC_PW h (c :: cs) (g :: gs)

end

--
-- Big-step multi-result supercompilation
--

-- Relational big-step multi-result supercompilation.

mutual

@[aesop unsafe [constructors, cases]]
inductive MRSC {α} [BEq α] {s : ScWorld α} {w : BarWhistle α} :
    (h : List α) -> (c : α) -> (g : Graph α) -> Prop where
  | fold {h c} :
      (f : s.FoldableToHistory c h) ->
        MRSC h c (.back c)
  | build {h c cs gs} :
      (nf : ¬s.FoldableToHistory c h) ->
      (nw : Not (w.dangerous h)) ->
      (i : cs ∈ s.develop c) ->
      (pw : MRSC_PW (c :: h) cs gs) ->
        MRSC h c (.forth c gs)

@[aesop unsafe [constructors, cases]]
inductive MRSC_PW {α} [BEq α] {s : ScWorld α} {w : BarWhistle α} :
      (h : List α) -> (cs : List α) -> (gs : List (Graph α)) -> Prop where
  | nil {h} : MRSC_PW h [] []
  | cons {h c g cs gs} :
      (p : MRSC h c g) -> (pw : MRSC_PW h cs gs) ->
        MRSC_PW h (c :: cs) (g :: gs)

end

--
-- Functional big-step multi-result supercompilation.
-- (The naive version builds Cartesian products immediately.)
--

def naive_mrsc' {α} (s : ScWorld α) (w : BarWhistle α)
      (h : List α) (b : Bar w.dangerous h) (c : α) : List (Graph α)
  :=
  match s.foldableToHistory? c h with
  | isTrue _ => [ .back c ]
  | isFalse _ => match w.dangerous? h with
      | .isTrue _ => []
      | .isFalse nd => match b with
          | .now d => False.elim (nd d)
          | .later bs =>
              ((s.develop c).flatMap
                (cartesian ∘ List.map (naive_mrsc' s w (c :: h) (bs c)))).map (.forth c)

def naive_mrsc {α} (s : ScWorld α) (w : BarWhistle α) (c : α) : List (Graph α)
  := naive_mrsc' s w [] w.barNil c

-- "Lazy" multi-result supercompilation.
-- (Cartesian products are not immediately built.)

-- lazy_mrsc is essentially a "staged" version of naive-mrsc
-- with get-graphs being an "interpreter" that evaluates the "program"
-- returned by lazy_mrsc.

def lazy_mrsc' {α} (s : ScWorld α) (w : BarWhistle α)
      (h : List α) (b : Bar w.dangerous h) (c : α) : LazyGraph α
  :=
  match s.foldableToHistory? c h with
  | .isTrue _ => .stop c
  | .isFalse _ => match w.dangerous? h with
      | .isTrue _ => .empty
      | .isFalse nd => match b with
          | .now d => False.elim (nd d)
          | .later bs =>
              .build c $
                (s.develop c).map (List.map (lazy_mrsc' s w (c :: h) (bs c)))

-- lazy_mrsc

def lazy_mrsc (s : ScWorld α) (w : BarWhistle α) (c : α) : LazyGraph α
  := lazy_mrsc' s w [] w.barNil c
