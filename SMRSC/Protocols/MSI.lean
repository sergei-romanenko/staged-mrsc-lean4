--
-- SMRSC.Protocols.MSI
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def MSI : CountersWorld where
  k := 3

  start : Conf 3
    := ## [ω, #0, #0]

  rules : (c : Conf 3) -> List (Bool × Conf 3)
    | i :: m :: s :: ε => [
      (i >=# 1, ## [i + m + s - #1, #1, #0]),
      (s >=# 1, ## [i + m + s - #1, #1, #0]),
      (i >=# 1, ## [i - #1, #0, m + s + #1])]

  unsafe? : (c : Conf 3) -> Bool
    | _ :: m :: s :: ε =>
      (m >=# 1 && s >=# 1) || (m >=# 2)

namespace TestMSI

def expected : String
:= "\
MSI (3, 58)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 1, 0]
      |
      |__[W, 1, 0]*
      |
      |__[W, 0, 2]*
    |
    |__[W, 1, 0]
      |
      |__[W, 1, 0]*
      |
      |__[W, 0, 2]*
    |
    |__[W, 0, W]*
"

#guard run_min_sc "MSI" MSI 3 10 == expected

#guard run_min_sc8 "MSI" MSI 3 10 == expected

end TestMSI
