--
-- SMRSC.GraphsTheorems
--

--
-- Graphs of configurations
--

import Batteries
import Aesop

import SMRSC.Util
import SMRSC.Graphs

--
-- Lemmas
--

@[simp]
theorem rw_unroll_cl_empty {α} (c: α) : (lss : List (List (LazyGraph α))) ->
  unroll (cl_empty_build c lss) = unroll (.build c lss)
  | [] => rfl
  | _ :: _ => rfl

@[simp]
theorem  rw_unroll_empty {α} :
  unroll (α := α) .empty = []
:= rfl

@[simp]
theorem  rw_unroll_stop {α} {c : α} :
  unroll (.stop c) = [ .back c ]
:= rfl

@[simp]
theorem  rw_unroll_build {α} {c : α} (lss : List (List (LazyGraph α))) :
  unroll (.build c lss) = List.map (.forth c) (unroll_lss lss)
:= rfl

@[simp]
theorem rw_unroll_lss_nil {α} : unroll_lss (α := α) [] = []
  := rfl

@[simp]
theorem rw_unroll_lss_cons {α} {ls : List (LazyGraph α)} {lss : List (List (LazyGraph α))} :
    unroll_lss (ls :: lss) = cartesian (unroll_ls ls) ++ unroll_lss lss
  := rfl

@[simp]
theorem rw_unroll_ls_nil {α} : unroll_ls (α := α) [] = []
  := rfl

@[simp]
theorem rw_unroll_ls_cons {α} {l : LazyGraph α} {ls : List (LazyGraph α)} :
    unroll_ls (l :: ls) = unroll l :: unroll_ls ls
  := rfl

@[simp]
theorem rw_cl_empty_empty {α} :
    cl_empty (α := α) (.empty) = .empty
:= by rw [cl_empty]

@[simp]
theorem rw_cl_empty_stop {α c} :
    cl_empty (α := α) (.stop c) = .stop c
:= by rw [cl_empty]

@[simp]
theorem rw_cl_empty_build {α c} {lss : List (List (LazyGraph α))} :
    cl_empty (.build c lss) = cl_empty_build c (cl_empty_lss lss)
:= by rw [cl_empty]

@[simp]
theorem rw_cl_empty_lss_nil {α}
    {ls : List (LazyGraph α)} {lss : List (List (LazyGraph α))}
    (eq : cl_empty_ls ls = .none) : cl_empty_lss (ls :: lss) = cl_empty_lss lss
:= by
  rw [cl_empty_lss, eq]

@[simp]
theorem rw_cl_empty_lss_cons {α}
    {ls ls' : List (LazyGraph α)} {lss : List (List (LazyGraph α))}
    (eq : cl_empty_ls ls = .some ls') : cl_empty_lss (ls :: lss) = ls' :: cl_empty_lss lss
:= by
  rw [cl_empty_lss, eq]

@[simp]
theorem rw_cl_empty_ls_nil {α}: cl_empty_ls (α := α) [] = .some []
:= by
  rw [cl_empty_ls]

@[simp]
theorem rw_cl_empty_ls_cons {α}
    {l : LazyGraph α} {ls : List (LazyGraph α)}
    (eq : cl_empty l = .empty) : cl_empty_ls (l :: ls) = .none
:= by
  rw [cl_empty_ls, eq]

@[simp]
theorem rw_cl_empty_ls_cons_ls {α}
    {l : LazyGraph α} {ls : List (LazyGraph α)}
    (eq : cl_empty_ls ls = .none) : cl_empty_ls (l :: ls) = .none
:= by
  match app_eq cl_empty l with
  | ⟨.empty, eq_l'⟩ =>
      rw [rw_cl_empty_ls_cons eq_l']
  | ⟨.stop c, eq_l'⟩ =>
      simp only [cl_empty_ls, eq_l', cl_empty_ls', eq]
  | ⟨.build c lss, eq_l'⟩ =>
      simp only [cl_empty_ls, eq_l', cl_empty_ls', eq]

--
-- `cl_empty` is correct
--

mutual

theorem cl_empty_correct {α} : (l : LazyGraph α) ->
      unroll (cl_empty l) = unroll l
  | .empty => by
      simp only [rw_cl_empty_empty, rw_unroll_empty]
  | .stop c => by
      simp only [rw_cl_empty_stop, rw_unroll_stop]
  | .build c lss => by
      simp only [rw_cl_empty_build, rw_unroll_cl_empty, rw_unroll_build,
                  cl_empty_lss_correct]

theorem cl_empty_lss_correct {α} : (lss : List (List (LazyGraph α))) ->
      unroll_lss (cl_empty_lss lss) = unroll_lss lss
  | [] => by simp only [cl_empty_lss, rw_unroll_lss_nil]
  | ls :: lss => by
      let ols' := cl_empty_ls ls
      have eq_ols' : cl_empty_ls ls = ols' := rfl
      match ols' with
      | none =>
          rw [cl_empty_lss, eq_ols', rw_unroll_lss_cons,
              cl_empty_none ls eq_ols', List.nil_append,
              cl_empty_lss_correct]
      | some ls' =>
          rw [cl_empty_lss, eq_ols', rw_unroll_lss_cons, rw_unroll_lss_cons,
              cl_empty_some ls ls' eq_ols', cl_empty_lss_correct]

theorem cl_empty_none {α} : (ls : List (LazyGraph α)) ->
    cl_empty_ls ls = none -> cartesian (unroll_ls ls) = []
  | [], eq => by simp at eq
  | l :: ls, eq => by
      match app_eq cl_empty l with
      | ⟨.empty, eq_l'⟩ =>
          rw [rw_unroll_ls_cons, cartesian, <- cl_empty_correct, eq_l',
              rw_unroll_empty, cartesian2]
      | ⟨.stop c, eq_l'⟩ =>
          match app_eq cl_empty_ls ls with
          | ⟨.none, cl_ls_none⟩ =>
              rw [rw_unroll_ls_cons, cartesian,
                  cl_empty_none ls cl_ls_none, rw_cartesian2_nil]
          | ⟨.some ls', cl_ls_some⟩ =>
              simp [cl_empty_ls, cl_empty_ls', cl_ls_some, eq_l'] at eq

      | ⟨.build _ _, eq_l'⟩ =>
          match app_eq cl_empty_ls ls with
          | ⟨.none, cl_ls_none⟩ =>
              rw [rw_unroll_ls_cons, cartesian,
                  cl_empty_none ls cl_ls_none, rw_cartesian2_nil]
          | ⟨.some ls', cl_ls_some⟩ =>
              simp [cl_empty_ls, cl_empty_ls', cl_ls_some, eq_l'] at eq

theorem cl_empty_some {α} : (ls ls' : List (LazyGraph α)) ->
      cl_empty_ls ls = some ls' -> cartesian (unroll_ls ls) = cartesian (unroll_ls ls')
  | [], ls', eq => by
      simp at eq
      simp [eq]
  | l :: ls, ls', eq => by
      match app_eq cl_empty l with
      | ⟨.empty, eq_l'⟩ =>
          simp only [eq_l', rw_cl_empty_ls_cons, reduceCtorEq] at eq
      | ⟨.stop c, eq_l'⟩ =>
          match app_eq cl_empty_ls ls with
          | ⟨.none, cl_ls_none⟩ =>
              simp [cl_ls_none, rw_cl_empty_ls_cons_ls] at eq
          | ⟨.some ls'', cl_ls_some⟩ =>
              simp [cl_empty_ls, cl_empty_ls', cl_ls_some, eq_l'] at eq
              simp [cartesian]
              rw [<- cl_empty_correct, eq_l', unroll, <- eq, unroll_ls, unroll,
                  cartesian, cl_empty_some ls ls'' cl_ls_some]
      | ⟨.build _ _, eq_l'⟩ =>
          match app_eq cl_empty_ls ls with
          | ⟨.none, cl_ls_none⟩ =>
              simp [cl_ls_none, rw_cl_empty_ls_cons_ls] at eq
          | ⟨.some ls'', cl_ls_some⟩ =>
              simp [cl_empty_ls, cl_empty_ls', cl_ls_some, eq_l'] at eq
              simp [cartesian]
              rw [<- cl_empty_correct, eq_l', unroll, <- eq, unroll_ls, unroll,
                  cartesian, cl_empty_some ls ls'' cl_ls_some]

end
