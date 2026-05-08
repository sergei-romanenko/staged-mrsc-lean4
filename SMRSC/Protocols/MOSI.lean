--
-- SMRSC.Protocols.MOSI
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def MOSI : CountersWorld where
  k := 4

  start : Conf 4
    := ## [ω, #0, #0, #0]

  rules : (c : Conf 4) -> List (Bool × Conf 4)
    | i :: o :: s :: m :: ε => [
      (i >=# 1, ## [i - #1, m + o, s + #1, #0]),
      (o >=# 1, ## [i + o + s + m - #1, #0, #0, #1]),
      -- wI
      (i >=# 1, ## [i + o + s + m - #1, #0, #0, #1]),
      -- wS
      (s >=# 1, ## [i + o + s + m - #1, #0, #0, #1]),
      -- se
      (s >=# 1, ## [i + #1, o, s - #1, m]),
      -- wbm
      (m >=# 1, ## [i + #1, o, s, m - #1]),
      -- wbo
      (o >=# 1, ## [i + #1, o - #1, s, m])]

  unsafe? : (c : Conf 4) -> Bool
    | _ :: o :: s :: m :: ε =>
      (o >=# 2) || (m >=# 2) || (s >=# 1 && m >=# 1)

def expected : String
:= "\
MOSI (459, 53802)
|__[W, 0, 0, 0]
  |
  |__[W, 0, W, 0]
    |
    |__[W, 0, W, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]
        |
        |__[W, 1, W, 0]
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, W, 0]*
      |
      |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]
        |
        |__[W, 1, W, 0]
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 0, 0, 1]*
          |
          |__[W, 1, W, 0]*
          |
          |__[W, 0, W, 0]*
      |
      |__[W, 0, 0, 1]*
      |
      |__[W, 0, 0, 0]*
    |
    |__[W, 0, W, 0]*
"

#guard run_min_sc "MOSI" MOSI 3 10 == expected

#guard run_min_sc8 "MOSI" MOSI 3 10 == expected
