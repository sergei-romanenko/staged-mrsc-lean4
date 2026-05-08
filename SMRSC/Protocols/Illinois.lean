--
-- SMRSC.Protocols.Illinois
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def Illinois : CountersWorld where
  k := 4

  start : Conf 4
    := ## [ω, #0, #0, #0]

  rules : (c : Conf 4) -> List (Bool × Conf 4)
    | i :: e :: d :: s :: ε => [
      -- r2
      (i >=# 1 && e =# 0 && d =# 0 && s =# 0,
          ## [i - #1, #1, #0, #0]),
      -- r3
      (i >=# 1 && d >=# 1,
          ## [i - #1, e, d - #1, s + #2]),
      -- r4
      (i >=# 1 && s + e >=# 1,
          ## [i - #1, #0, d, s + e + #1]),
      -- r6
      (e >=# 1,
          ## [i, e - #1, d + #1, s]),
      -- r7
      (s >=# 1,
          ## [i + s - #1, e, d + #1, #0]),
      -- r8
      (i >=# 1,
          ## [i + e + d + s - #1, #0, #1, #0]),
      -- r9
      (d >=# 1,
          ## [i + #1, e, d - #1, s]),
      -- r10
      (s >=# 1,
          ## [i + #1, e, d, s - #1]),
      -- r11
      (e >=# 1,
          ## [i + #1, e - #1, d, s])]

  unsafe? : (c : Conf 4) -> Bool
    | _ :: _ :: d :: s :: ε =>
      (d >=# 1 && s >=# 1) || (d >=# 2)

namespace TestIllinois

def expected : String
:= "\
Illinois (2, 73)
|__[W, 0, 0, 0]
  |
  |__[W, 0, 0, W]
    |
    |__[W, 1, 0, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]
        |
        |__[W, 0, 0, 2]*
        |
        |__[W, 0, 1, 0]*
        |
        |__[W, 0, 0, 0]*
      |
      |__[W, 0, 1, 0]
        |
        |__[W, 0, 0, 2]*
        |
        |__[W, 0, 1, 0]*
        |
        |__[W, 0, 0, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, W]*
    |
    |__[W, 0, 1, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 1, 0]
      |
      |__[W, 0, 0, 2]*
      |
      |__[W, 0, 1, 0]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, W]*
"

-- #guard  run_min_sc "Illinois" Illinois 3 10 == expected

#guard run_min_sc8 "Illinois" Illinois 3 10 == expected

end TestIllinois
