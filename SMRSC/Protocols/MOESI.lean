--
-- SMRSC.Protocols.MOESI
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def MOESI : CountersWorld where
  k := 5

  start : Conf 5
    := ## [ω, #0, #0, #0, #0]

  rules : (c : Conf 5) -> List (Bool × Conf 5)
    | i :: m :: s :: e :: o :: ε => [
      -- rm
      (i >=# 1, ## [i - #1, #0, s + e + #1, #0, o + m]),
      -- wh2
      (e >=# 1, ## [i, m + #1, s, e - #1, o]),
      -- wh3
      (s + o >=# 1, ## [i + m + s + e + o - #1, #0, #0, #1, #0]),
      -- wm
      (i >=# 1, ## [i + m + s + e + o - #1, #0, #0, #1, #0])]

  unsafe? : (c : Conf 5) -> Bool
    | _ :: m :: s :: e :: o :: ε =>
      (m >=# 1 && (e + s + o) >=# 1) || (m >=# 2) || (e >=# 2)

namespace TestMOESI

def expected : String
:= "\
MOESI (3944820, 312092974)
|__[W, 0, 0, 0, 0]
  |
  |__[W, 0, W, 0, W]
    |
    |__[W, 0, W, 0, W]*
    |
    |__[W, 0, 0, 1, 0]
      |
      |__[W, 0, 2, 0, 0]*
      |
      |__[W, 1, 0, 0, 0]
        |
        |__[W, 0, 1, 0, 1]*
        |
        |__[W, 0, 0, 1, 0]*
      |
      |__[W, 0, 0, 1, 0]*
    |
    |__[W, 0, 0, 1, 0]
      |
      |__[W, 0, 2, 0, 0]*
      |
      |__[W, 1, 0, 0, 0]
        |
        |__[W, 0, 1, 0, 1]*
        |
        |__[W, 0, 0, 1, 0]*
      |
      |__[W, 0, 0, 1, 0]*
"

-- #guard run_min_sc "MOESI" MOESI 3 10 == expected

#guard run_min_sc8 "MOESI" MOESI 3 10 == expected

end TestMOESI
