--
-- SMRSC.Protocols.Xerox
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics


open NW (ω)
open Vec (ε)

def Xerox : CountersWorld where
  k := 5

  start : Conf 5
    := ## [ω, #0, #0, #0, #0]

  rules : (c : Conf 5) -> List (Bool × Conf 5)
    | i :: sc :: sd :: d :: e :: ε => [
      -- (1) rm1
      (i >=# 1 && d =# 0 && sc =# 0 && sd =# 0 && e =# 0,
          ## [i - #1, #0, #0, #0, #1]),
      -- (2) rm2
      (i >=# 1 && d + sc + e + sd >=# 1,
          ## [i - #1, sc + e + #1, sd + d, #0, #0]),
      -- (3) wm1
      (i >=# 1 && d =# 0 && sc =# 0 && sd =# 0 && e =# 0,
          ## [i - #1, #0, #0, #1, #0]),
      -- (4) wm2
      (i >=# 1 && d + sc + e + sd >=# 1,
          ## [i - #1, sc + e + #1 + (sd + d), sd, #0, #0]),
      -- (5) wh1
      (d >=# 1,
          ## [i + #1, sc, sd, d - #1, e]),
      -- (6) wh2
      (sc >=# 1,
          ## [i + #1, sc - #1, sd, d, e]),
      -- (7) wh3
      (sd >=# 1,
          ## [i + #1, sc, sd - #1, d, e]),
      -- (8) wh4
      (e >=# 1,
          ## [i + #1, sc, sd, d, e - #1])]

  unsafe? : (c : Conf 5) -> Bool
    | _ :: sc :: sd :: d :: e :: ε =>
      (e >=# 1 && (sc + sd) >=# 1) ||
      (d >=# 2) ||
      (e >=# 2)

namespace TestXerox

def expected : String
:= "\
Xerox (10305306, 1278733438)
|__[W, 0, 0, 0, 0]
  |
  |__[W, W, W, 0, 0]
    |
    |__[W, 0, 0, 0, 1]
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 0, 0, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, 0, 0, 1, 0]
      |
      |__[W, 1, 1, 0, 0]*
      |
      |__[W, 2, 0, 0, 0]*
      |
      |__[W, 0, 0, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
    |
    |__[W, W, W, 0, 0]*
"

-- #guard run_min_sc "Xerox" Xerox 3 10 == expected

#guard run_min_sc8 "Xerox" Xerox 3 10 == expected

end TestXerox
