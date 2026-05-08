--
-- SMRSC.Protocols.MESI
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def MESI : CountersWorld where
  k := 4

  start : Conf 4
    := ## [ω, #0, #0, #0]

  rules : (c : Conf 4) -> List (Bool × Conf 4)
    | i :: e :: s :: m :: ε => [
      (i >=# 1, ## [i - #1, #0, s + e + m + #1, #0]),
      (e >=# 1, ## [i, e - #1, s, m + #1]),
      (s >=# 1, ## [i + e + s + m - #1, #1, #0, #0]),
      (i >=# 1, ## [i + e + s + m - #1, #1, #0, #0])]

  unsafe? : (c : Conf 4) -> Bool
    | _ :: _ :: s :: m :: ε =>
      m >=# 2 || (s >=# 1 && m >=# 1)

namespace TestMESI

def expected : String
:= "\
MESI (3, 104)
|__[W, 0, 0, 0]
  |
  |__[W, 0, W, 0]
    |
    |__[W, 0, W, 0]*
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 1, 0, 0]*
      |
      |__[W, 1, 0, 0]*
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 2, 0]*
      |
      |__[W, 0, 0, 1]
        |
        |__[W, 0, 2, 0]*
        |
        |__[W, 1, 0, 0]*
      |
      |__[W, 1, 0, 0]*
"

#guard run_min_sc "MESI" MESI 3 10 == expected

#guard run_min_sc8 "MESI" MESI 3 10 == expected

end TestMESI
