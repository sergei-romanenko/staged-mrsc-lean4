--
-- Graphs of configurations
--

-- SMRSC.Graphs

import Batteries
import Aesop

import SMRSC.Util

--
-- Graphs of configurations
--

-- A `Graph α` is supposed to represent a residual program.
-- Technically, a `Graph α` is a tree, with `back` nodes being
-- references to parent nodes.
--
-- A graph's nodes contain configurations. Here we abstract away
-- from the concrete structure of configurations.
-- In this model the arrows in the graph carry no information,
-- because this information can be kept in nodes.
-- (Hence, this information is supposed to be encoded inside
-- "configurations".)
--
-- To simplify the machinery, back-nodes in this model of
-- supercompilation do not contain explicit references
-- to parent nodes. Hence, `back c` means that `c` is foldable
-- to a parent configuration (perhaps, to several ones).
--
-- * back-nodes are produced by folding a configuration to another
--   configuration in the history.
-- * forth-nodes are produced by
--     + decomposing a configuration into a number of other configurations
--       (e.g. by driving or taking apart a let-expression), or
--     + by rewriting a configuration by another one (e.g. by generalization,
--       introducing a let-expression or applying a lemma during
--       two-level supercompilation).

-- Graph

inductive Graph (α : Type) : Type where
  | back  : (c : α) -> Graph α
  | forth : (c : α) -> (gs : List (Graph α)) -> Graph α
deriving BEq, Repr

--
-- Lazy graphs of configuration
--

-- A `LazyGraph α` represents α finite set of graphs
-- of configurations (whose type is `Graph α`).
--
-- "Lazy" graphs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyGraph

inductive LazyGraph (α : Type) : Type where
  | empty : LazyGraph α
  | stop  : (c : α) -> LazyGraph α
  | build : (c : α) -> (lss : List (List (LazyGraph α))) -> LazyGraph α
deriving BEq, Repr

-- empty?

def empty? {c} : (l : LazyGraph c) -> Decidable (.empty = l)
  | .empty => isTrue rfl
  | .stop _ => isFalse (nomatch ·)
  | .build _ _ => isFalse (nomatch ·)

-- The semantics of a `LazyGraph α` is formally defined by
-- the interpreter `unroll` that generates a list of `Graph α` from
-- the `LazyGraph α` by executing commands recorded in the `LazyGraph α`.

mutual

def unroll {α} : (l : LazyGraph α) -> List (Graph α)
  | .empty => []
  | .stop c =>  [ .back c ]
  | .build c lss => List.map (.forth c) (unroll_lss lss)

  def unroll_lss {α} : (lss : List (List (LazyGraph α))) -> List (List (Graph α))
    | [] => []
    | (ls :: lss) => cartesian (unroll_ls ls) ++ unroll_lss lss

  -- `unroll_ls` has only been introduced to make the termination
  -- checker happy. Actually, it is equivalent to `map unroll`.

def unroll_ls {α} : (ls : List (LazyGraph α)) -> List (List (Graph α))
  | [] => []
  | (l :: ls) => unroll l :: unroll_ls ls

end


--
-- Usually, we are not interested in the whole bag `unroll l`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C` without evaluating
-- `unroll l` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select (unroll l)
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract l = select (unroll l)
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnitude) than the composition `select . unroll`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     unroll (clean l) ⊆ unroll l
--
-- Then `extract` can be constructed in the following way:
--
--     extract l = unroll (clean l)
--
-- Theoretically speaking, `clean` is the result of "promoting" `select`:
--
--     select . unroll ≗ unroll . clean
--
-- The nice property of cleaners is that they are composable:
-- given `clean₁` and `clean₂`, `clean₂ . clean₁` is also a cleaner.
--

--
-- Some filters
--

-- Removing graphs that contain "bad" configurations.
-- Configurations represent states of a computation process.
-- Some of these states may be "bad" with respect to the problem
-- that is to be solved by means of supercompilation.

mutual

def bad_graph {α} (bad : α -> Bool) : (g : Graph α) -> Bool
  | .back c => bad c
  | .forth c gs => bad c || bad_graph_gs bad gs

def bad_graph_gs {α} (bad : α -> Bool) : (gs : List (Graph α)) -> Bool
  | [] => false
  | g :: gs => bad_graph bad g || bad_graph_gs bad gs

end

-- This filter removes the graphs containing "bad" configurations.

def fl_bad_conf {α} (bad : α -> Bool) (gs : List (Graph α)) : List (Graph α)
  := List.filter (not ∘ bad_graph bad) gs

--
-- Some cleaners
--

-- `cl_empty` removes subtrees that represent empty sets of graphs.

def cl_empty_build {α} (c : α) : List (List (LazyGraph α)) -> LazyGraph α
  | [] => .empty
  | ls :: lss => .build c (ls :: lss)

mutual

def cl_empty {α} : (l : LazyGraph α) -> LazyGraph α
  | .empty => .empty
  | .stop c => .stop c
  | .build c lss => cl_empty_build c (cl_empty_lss lss)

def cl_empty_lss {α} : (lss : List (List (LazyGraph α))) ->  List (List (LazyGraph α))
  | [] => []
  | ls :: lss =>
      match cl_empty_ls ls with
      | .none => cl_empty_lss lss
      | .some ls' => ls' :: cl_empty_lss lss

def cl_empty_ls {α} : (ls : List (LazyGraph α)) -> Option (List (LazyGraph α))
  | [] => .some []
  | l :: ls =>
      let l' := cl_empty l
      match empty? l' with
      | isTrue _ => .none
      | isFalse _ => match cl_empty_ls ls with
          | .none => .none
          | .some ls' => .some (l' :: ls')

end

-- Removing graphs that contain "bad" configurations.
-- The cleaner `cl_bad_conf` corresponds to the filter `fl_bad_conf`.
-- `cl_bad_conf` exploits the fact that "badness" is monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph.

mutual

def cl_bad_conf {α} (bad : α -> Bool) : (l : LazyGraph α) -> LazyGraph α
  | .empty => .empty
  | .stop c =>
      if bad c then .empty else (.stop c)
  | .build c lss =>
      if bad c then .empty else (.build c (cl_bad_conf_lss bad lss))

def cl_bad_conf_lss {α} (bad : α -> Bool) :
      (lss : List (List (LazyGraph α))) -> List (List (LazyGraph α))
  | [] => []
  | ls :: lss =>
      cl_bad_conf_ls bad ls :: (cl_bad_conf_lss bad lss)

def cl_bad_conf_ls {α} (bad : α -> Bool) :
      (ls : List (LazyGraph α)) -> List (LazyGraph α)
  | [] => []
  | l :: ls =>
      cl_bad_conf bad l :: cl_bad_conf_ls bad ls

end

--
-- The graph returned by `cl_bad_conf` may be cleaned by `cl_empty`.
--

def cl_empty_and_bad {α} (bad : α -> Bool) : (l : LazyGraph α) -> LazyGraph α
  := cl_empty ∘ cl_bad_conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

def graph_size {α} : (g : Graph α) -> Nat
  | .back _ => 1
  | .forth _ gs => graph_size_gs gs + 1

def graph_size_gs {α} : (gs : List (Graph α)) -> Nat
  | [] => 0
  | g :: gs => graph_size g + graph_size_gs gs

end

-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , empty).

def select_min2 {α} : (kx1 kx2 : Nat × α) -> Nat × α
  | (0, _), (k2, x2) => (k2, x2)
  | (k1, x1), (0, _) => (k1, x1)
  | (k1, x1), (k2, x2) =>
      if k1 <= k2 then (k1, x1) else (k2, x2)

def select_min {α} (c : α) : (kxs : List (Nat × α)) -> Nat × α
  | [] => (0 , c)
  | (kgs :: kgss) => kgss.foldl select_min2 kgs

mutual

def cl_min_size {α} : (l : LazyGraph α) -> Nat × LazyGraph α
  | .empty =>
      (0 , .empty)
  | .stop c =>
      (1 , .stop c)
  | .build c lss => match cl_min_size2 lss with
      | (0 , _) => (0 , .empty)
      | (k , ls) => (k + 1 , .build c [ ls ])

def cl_min_size2 {α} : (lss : List (List (LazyGraph α))) ->
    Nat × List (LazyGraph α)
  | [] => (0, [])
  | ls :: lss =>
      let kls1 := cl_min_size_and ls
      let kls2 := cl_min_size2 lss
      select_min2 kls1 kls2

def cl_min_size_and {α} : (ls : List (LazyGraph α)) ->
      Nat × List (LazyGraph α)
  | [] => (1, [])
  | l :: ls => match cl_min_size l, cl_min_size_and ls with
      | (0, l'), (_, ls') => (0 , l' :: ls')
      | (_, l'), (0, ls') => (0 , l' :: ls')
      | (i, l'), (j, ls') => (i + j , l' :: ls')

end

--
-- `cl_min_size` is sound:
--
--  Let cl_min_size l = (k , l'). Then
--     unroll l' ⊆ unroll l
--     k = graph_size (hd (unroll l'))
--
-- TODO: prove this formally

--
-- Graph.toString
--

mutual

def tsGraph {α} [ToString α] : Graph α -> String := fun
  | .back c => s!"back {c}"
  | .forth c gs => s!"forth {c} [{tsGraph_gs "" gs}]"

def tsGraph_gs {α} [ToString α] (acc : String) : List (Graph α) -> String
:= fun
  | [] => acc
  | g :: gs =>
      let acc' := acc ++ tsGraph g
      if gs.isEmpty then acc' else tsGraph_gs (acc' ++ ", ") gs

end

instance {α} [ToString α] : ToString (Graph α) where
  toString := tsGraph

mutual

def tsLazyGraph {α} [ToString α] : LazyGraph α -> String
:= fun
  | .empty => "empty"
  | .stop c => s!"stop {c}"
  | .build c lss =>
      s!"build {c} [{tsLazyGraph_lss "" lss}]"

def tsLazyGraph_lss {α} [ToString α] (acc : String) : List (List (LazyGraph α)) -> String
  | [] => acc
  | ls :: lss =>
      let acc' :=  s!"{acc}[{tsLazyGraph_ls "" ls}]"
      if lss.isEmpty then acc' else tsLazyGraph_lss (acc' ++ ", ") lss

def tsLazyGraph_ls {α} [ToString α] (acc : String) : List (LazyGraph α) -> String
  | [] => acc
  | l :: ls =>
      let acc' := acc ++ tsLazyGraph l
      if ls.isEmpty then acc' else tsLazyGraph_ls (acc' ++ ", ") ls

end

instance {α} [ToString α] : ToString (LazyGraph α) where
  toString := tsLazyGraph

--
-- Pretty-printing
--

-- Graph pretty-printer

mutual

def graph_pp_g {α} [ToString α] (indent : String) : (g : Graph α) -> String
  | .back c =>
      s!"{indent}|__{c}*"
  | .forth c gs =>
      graph_pp_gs s!"{indent}|__{c}" indent gs

def graph_pp_gs {α} [ToString α] (acc : String) (indent : String) :
      (gs : List (Graph α)) -> String
  | [] => acc
  | g :: gs =>
      graph_pp_gs
        s!"{acc}\n  {indent}|\n{graph_pp_g (indent ++ "  ") g}"
        indent gs

end

def graph_pp {α} [ToString α] (g : Graph α) : String
  := graph_pp_g "" g
