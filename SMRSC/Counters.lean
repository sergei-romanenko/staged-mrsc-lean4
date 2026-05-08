--
-- module SMRSC.Counters
--

import Batteries
import Aesop

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Cographs
import SMRSC.Statistics

-- NW

@[aesop unsafe [constructors, cases]]
inductive NW : Type where
  | ω   : NW
  | n : (i : Nat) -> NW
deriving BEq, DecidableEq, Repr

open NW (ω)

prefix:1024 "#" => NW.n

instance : ToString NW where
  toString := fun
    | .ω => "W"
    | .n i => toString i

-- m + n

instance : Add NW where
  add := fun
    | .ω, _ => ω
    | _, ω => ω
    | .n i, .n j => #(i + j)

-- m - n

instance : Sub NW where
  sub := fun
    | ω, _ => ω
    | _, ω => ω
    | .n i, .n j => #(i - j)

-- gte_cn

@[aesop unsafe [constructors, cases]]
inductive gte_cn : (m : NW) -> (j : Nat) -> Prop where
  | wn {j} : gte_cn ω j
  | nn {i j} : i ≥ j -> gte_cn (#i) j

-- gte_cn?

def gte_cn? : (m : NW) -> (j : Nat) -> Decidable (gte_cn m j)
  | .ω, _ => isTrue gte_cn.wn
  | .n i, j =>
      if h : i ≥ j then
        isTrue $ gte_cn.nn h
      else
        isFalse $ fun | .nn ge_i_j => False.elim (h ge_i_j)

instance : DecidableRel gte_cn := gte_cn?

-- eq_cn

inductive eq_cn : (m : NW) -> (j : Nat) -> Prop where
  | wn {j} : eq_cn ω j
  | nn {j} : eq_cn #j j

-- eq_cn?

def eq_cn? : (m : NW) -> (j : Nat) -> Decidable (eq_cn m j)
  | .ω, j => isTrue eq_cn.wn
  | .n i, j =>
      if eq? : i = j then
        isTrue $ by subst eq?; exact eq_cn.nn
      else
        isFalse $ fun | .nn => nomatch eq?

instance : DecidableRel eq_cn := eq_cn?

-- m `is_in` n means that n is more general than m.

-- is_in

inductive is_in : (m n : NW) -> Prop where
  | in_w {m} : is_in m ω
  | in_n {i} : is_in #i #i

-- is_in?

def is_in? : (m n : NW) -> Decidable (is_in m n)
  | m, .ω => isTrue $ is_in.in_w
  | ω, .n j => isFalse (nomatch ·)
  | #i, #j =>
      if eq? : i = j then
        isTrue $ by subst eq?; exact is_in.in_n
      else
        isFalse fun | .in_n => nomatch eq?

instance (m n : NW) : Decidable (is_in m n)
  := is_in? m n

--
-- "Worlds of counters"
-- (To be converted to worlds of supercompilation.)
--

inductive Vec (α : Type) : (k : Nat) -> Type where
  | ε : Vec α 0
  | cons {k} : α -> Vec α k -> Vec α (k + 1)
deriving BEq, Repr

infixr:67 " :: " => Vec.cons

namespace Vec

def map {α β k} (f : α -> β) : Vec α k -> Vec β k
  | .ε => .ε
  | x :: xs => f x :: map f xs

def toList {α k} : Vec α k -> List α
  | .ε => []
  | x :: xs => x :: xs.toList

def toString {α k} [ToString α] (xs : Vec α k) : String
  :=
  let xs_string := String.intercalate ", " $ xs.toList.map (fun x => s!"{x}")
  s!"[{xs_string}]"

end Vec

instance {α k}  [ToString α] : ToString (Vec α k) where
  toString xs := Vec.toString xs

abbrev Conf (k : Nat) := Vec NW k

def List.toVec {α} : (ns : List α) -> Vec α ns.length
  | [] => .ε
  | x :: xs => x :: List.toVec xs

/-
instance {α} {ns} : CoeDep (List α) ns (Vec α ns.length) where
  coe := ns.toVec
 -/

prefix:1024 "##" => List.toVec

structure CountersWorld where

  k : Nat

  -- Initial configuration
  start : Conf k

  -- Driving rules
  rules : (c : Conf k) -> List (Bool × Conf k)

  -- Which configurations are (semantically) unsafe?
  unsafe? : (c : Conf k) -> Bool

--
-- Converting a world of counters to a world of supercompilation.
--

@[aesop unsafe [constructors, cases]]
inductive isFoldableTo : {k : Nat} -> (ms : Conf k) -> (ns : Conf k) -> Prop where
  | ε : isFoldableTo .ε .ε
  | cons {m n ms ns} : is_in m n -> isFoldableTo ms ns ->
      isFoldableTo (m :: ms) (n :: ns)

def cnt_isFoldableTo? {k : Nat} : (c c' : Conf k) -> Decidable (isFoldableTo c c')
  | .ε, .ε => isTrue $ isFoldableTo.ε
  | m :: ms, n :: ns => match is_in? m n with
      | isTrue in_m_n => match cnt_isFoldableTo? ms ns with
          | isTrue pw => isTrue $ .cons in_m_n pw
          | isFalse npw => isFalse $
              fun | .cons _ in_ms_ns => False.elim (npw in_ms_ns)
      | isFalse nin_m_n => isFalse $
          fun | .cons in_m_n _ => False.elim (nin_m_n in_m_n)

-- Rebuildings

def cnt_rebuild1 : (nw : NW) -> List NW
  | ω => [ ω ]
  | #i => [ #i, ω ]

-- vec_cartesian

def vec_cartesian2 {α k} : List α -> List (Vec α k) -> List (Vec α (k + 1))
  | [], _ => []
  | x :: xs, yss =>
      yss.map (.cons x) ++ vec_cartesian2 xs yss

def vec_cartesian {α k} : Vec (List α) k -> List (Vec α k)
  | .ε => [ .ε ]
  | xs :: xss => vec_cartesian2 xs (vec_cartesian xss)

def cntSc (cw : CountersWorld) : ScWorld (Conf cw.k)
:=
  let drive (c : Conf cw.k) : List (Conf cw.k) :=
    let prs := (cw.rules c).filter (fun (p, _) => p)
    prs.map (·.snd)
  let rebuild (c : Conf cw.k) : List (Conf cw.k) :=
    (vec_cartesian (Vec.map cnt_rebuild1 c)).filter (c != ·)
  let develop (c : Conf cw.k) : List (List (Conf cw.k)) :=
    [ drive c ] ++ (rebuild c).map ([·])
  ⟨isFoldableTo (k := cw.k), cnt_isFoldableTo? (k := cw.k), develop⟩

namespace CntWhistle

variable {k : Nat} (maxNat maxDepth : Nat)

def tooBig1 : (m : NW) -> Prop
  | ω => False
  | #i => maxNat ≤ i

def tooBig1? : DecidablePred (tooBig1 maxNat)
  | ω => isFalse id
  | #i => maxNat.decLe i

instance : DecidablePred (tooBig1 maxNat) := tooBig1? maxNat

def tooBig (c : Conf k) : Prop
  := c.toList.any_p (tooBig1 maxNat)

def tooBig? (c : Conf k) : Decidable (tooBig maxNat c)
  := c.toList.any_p? (tooBig1 maxNat)

instance (c : Conf k) : Decidable (tooBig maxNat c)
  := tooBig? maxNat c

def dangerous (h : List (Conf k)) : Prop
  := maxDepth ≤ h.length ∨ (h.any_p (tooBig maxNat))

def dangerous? (h : List (Conf k)) :
      Decidable (dangerous maxNat maxDepth h)
:=
  match maxDepth.decLe h.length with
  | isTrue d => isTrue $ Or.inl d
  | isFalse nd => match h.any_p? (tooBig maxNat) with
      | .isTrue b => isTrue $ Or.inr b
      | .isFalse nb => isFalse $ fun
          | Or.inl d => nd d
          | Or.inr b => nb b

instance (h : List (Conf k)) :
    Decidable (dangerous maxNat maxDepth h)
  := dangerous? maxNat maxDepth h

def bar : (m : Nat) -> (h : List (Conf k)) ->
      (d : m + h.length = maxDepth) -> Bar (dangerous maxNat maxDepth) h
  | 0, h, d => .now $ Or.inl $
      by subst d; rw [Nat.zero_add]; exact Nat.le_refl h.length
  | m + 1, h, d => .later $ fun c =>
      have := calc
            m + (c :: h).length
        _ = m + (h.length + 1)   := congrArg (m + ·) List.length_cons
        _ = (m + 1) + h.length   := Eq.symm (Nat.succ_add_eq_add_succ m h.length)
        _ = maxDepth             := d
      bar m (c :: h) this

-- The whistle is based on the combination of `pathLengthWhistle` and
-- `h.any_p tooBig`.

-- TODO: It is possible to construct a whistle based on the fact that
-- the set of configurations such that `Not (tooBig c)` is finite.

def barNil (maxDepth : Nat) : Bar (α := Conf k) (dangerous maxNat maxDepth) []
  := bar maxNat maxDepth maxDepth [] rfl

end CntWhistle

def cntWhistle (k : Nat) (maxNat : Nat) (maxDepth : Nat) : BarWhistle (Conf k)
  := ⟨CntWhistle.dangerous maxNat maxDepth,
      CntWhistle.dangerous? maxNat maxDepth,
      CntWhistle.barNil maxNat maxDepth⟩

def cl_unsafe (cw : CountersWorld) : (l : LazyGraph (Conf cw.k)) -> LazyGraph (Conf cw.k)
  := cl_bad_conf cw.unsafe?

def cl8_unsafe {G} (cw : CountersWorld) [LazyGraph8 (Conf cw.k) G] (g : G) : Cl8Bad (Conf cw.k) G
  := cl8_bad_conf cw.unsafe? g

--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

infix:50 " >=# " => fun m j => decide (gte_cn m j)
infix:50 " =# " => fun m j => decide (eq_cn m j)

---
--- Runners
---

def run_min_sc (name : String)
      (cw : CountersWorld) (m d : Nat) : String
:=
  let r := name ++ " "
  let s := cntSc cw
  let w := cntWhistle cw.k m d
  let l := lazy_mrsc s w cw.start
  let sl := cl_empty_and_bad cw.unsafe? l
  let (len_usl, size_usl) := size_unroll sl
  let r := s!"{r}({len_usl}, {size_usl})\n"
  let (_, ml) := cl_min_size sl
  let gs := unroll ml
  let r := r ++
    match gs with
      | [] => ": No solution"
      | (mg :: _) => graph_pp mg
  r ++ "\n"

def run_min_sc8 (name : String)
  (cw : CountersWorld) (m d : Nat) : String
:=
  let r := name ++ " "
  let s := cntSc cw
  let w := cntWhistle cw.k m d
  let l8 := build_graph8 s cw.start
  let sl8 := cl8_bad_conf cw.unsafe? l8
  let sl := prune0_graph8 w sl8
  let (len_usl, size_usl) := size_unroll sl
  let r := s!"{r}({len_usl}, {size_usl})\n"
  let (_, ml) := cl_min_size sl
  let gs := unroll ml
  let r := r ++
    match gs with
      | [] => ": No solution"
      | (mg :: _) => graph_pp mg
  r ++ "\n"
