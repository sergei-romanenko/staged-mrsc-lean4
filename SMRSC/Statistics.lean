--
-- SMRSC.Statistics
--

import SMRSC.Util
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc

--
-- Counting without generation
--

-- The main idea of staged supercompilation consists in
-- replacing the analysis of residual graphs with the analysis
-- of the program that generates the graphs.
--
-- Gathering statistics about graphs is just a special case of
-- such analysis. For example, it is possible to count the number of
-- residual graphs that would be produced without actually generating
-- the graphs.
--
-- Technically, we can define a function `length_unroll` that analyses
-- lazy graphs such that
--   length_unroll(l) == length(unroll(l))

-- length_unroll

mutual

def length_unroll {a} : (l : LazyGraph a) -> Nat
  | .empty => 0
  | .stop _ => 1
  | .build _ lss => length_unroll_lss lss

def length_unroll_lss {a} : (lss : List (List (LazyGraph a))) -> Nat
  | [] => 0
  | ls :: lss =>
      length_unroll_ls ls + length_unroll_lss lss

def length_unroll_ls {a} : (ls : List (LazyGraph a)) -> Nat
  | [] => 1
  | l :: ls =>
      length_unroll l * length_unroll_ls ls

end

--
-- Counting nodes in collections of graphs
--
-- Let us find a function `size_unroll`, such that
--   size_unroll(l) == length(unroll l) , sum (map graph_size (unroll l)))
--

-- size_unroll

mutual

def size_unroll : (l : LazyGraph a) -> Nat × Nat
  | .empty => (0 , 0)
  | .stop _ => (1, 1)
  | .build _ lss => size_unroll_lss lss

def size_unroll_lss : (lss : List (List (LazyGraph a))) -> Nat × Nat
  | [] => (0, 0)
  | ls :: lss =>
      let (k', n') := size_unroll_ls ls
      let (k, n) := size_unroll_lss lss
      (k' + k , k' + n' + n)

def size_unroll_ls : (ls : List (LazyGraph a)) -> Nat × Nat
  | [] => (1, 0)
  | l :: ls =>
      let (k', n') := size_unroll l
      let (k, n) := size_unroll_ls ls
      (k' * k , k' * n + k * n')

end
