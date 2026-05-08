--
-- SMRSC.Protocols.Synapse
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def Synapse : CountersWorld where
    k := 3

    start : Conf 3 := ## [ω, #0, #0]

    rules : (c : Conf 3) -> List (Bool × Conf 3)
      | i :: d :: v :: ε => [
      (i >=# 1, ## [i + d - #1, #0, v + #1]),
      (v >=# 1, ## [i + d + v - #1, #1, #0]),
      (i >=# 1, ## [i + d + v - #1, #1, #0])]

    unsafe? : (c : Conf 3) -> Bool
      | _ :: d :: v :: ε =>
      (d >=# 1) && (v >=# 1) || (d >=# 2)


--
-- Tests
--

def bw : BarWhistle (Conf 3)
  := cntWhistle 3 3 10

def sw : ScWorld (Conf 3)
  := cntSc Synapse

def graph : LazyGraph (Conf 3)
  := lazy_mrsc sw bw (Synapse.start)

#guard length_unroll graph == 112020

#guard size_unroll graph == (112020 , 4024002)

def graph_cl_unsafe : LazyGraph (Conf 3)
  := cl_empty $ cl_unsafe Synapse graph

-- Cographs

def cograph : GenG (Conf 3)
  := build_graph8 sw (Synapse.start)

def cograph_safe : Cl8Empty (Conf 3) (Cl8Bad (Conf 3) (GenG (Conf 3)))
  := cl8_empty (α := Conf 3) $ cl8_bad_conf (α := Conf 3) Synapse.unsafe? cograph

def cograph_pruned : LazyGraph (Conf 3)
  := cl_empty $ prune_graph8 bw cograph_safe

#guard graph_cl_unsafe == cograph_pruned

-- Removing empty subtrees while pruning.

def lgraph : LazyGraph (Conf 3)
  := cl_empty $ prune0_graph8 bw cograph_safe

#guard graph_cl_unsafe == lgraph

-- lu_lgraph : length_unroll lgraph = 5
-- lu_lgraph = Refl

#guard length_unroll lgraph == 5

#guard size_unroll lgraph == (5 , 97)

def lgraph_min_size := cl_min_size lgraph

#guard size_unroll ((lgraph_min_size).snd) = (1 , 9)

def graph_min_size := unroll (lgraph_min_size.snd)

--
-- Run!
--

def expected : String
:= "\
Synapse (5, 97)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 0, W]*
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 1]*
      |
      |__[W, 1, 0]*
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 1]*
      |
      |__[W, 1, 0]*\
"

#guard run_min_sc "Synapse" Synapse 3 10 == expected

#guard run_min_sc8 "Synapse" Synapse 3 10 == expected
