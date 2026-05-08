--
-- SMRSC.Protocols.Berkley
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def Berkley : CountersWorld where
  k := 4

  start : Conf 4
    := ## [ω, #0, #0, #0]

  rules : (c : Conf 4) -> List (Bool × Conf 4)
    | i :: n :: u :: e :: ε => [
      -- rm
      (i >=# 1, ## [i - #1, n + e, u + #1, #0]),
      -- wm
      (i >=# 1, ## [i + n + u + e - #1, #0, #0, #1]),
      -- wh1
      (n + u >=# 1, ## [i + n + u - #1, #0, #0, e + #1])]

  unsafe? : (c : Conf 4) -> Bool
    | _ :: n :: u :: e :: ε =>
      (e >=# 1 && u + n >=# 1) || (e >=# 2)

namespace TestBerkley

def expected : String
:= "\
Berkley (62247, 3135052)
|__[W, 0, 0, 0]
  |
  |__[W, W, W, 0]
    |
    |__[W, W, W, 0]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]*
      |
      |__[W, 0, 0, 1]*
    |
    |__[W, 0, 0, 1]
      |
      |__[W, 1, 1, 0]*
      |
      |__[W, 0, 0, 1]*
"

-- #guard run_min_sc "Berkley" Berkley 3 10 == expected

#guard run_min_sc8 "Berkley" Berkley 3 10 == expected

end TestBerkley
