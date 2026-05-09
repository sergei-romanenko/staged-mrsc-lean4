--
-- SMRSC.Protocols.DataRace
--

import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Counters
import SMRSC.Cographs
import SMRSC.Statistics

open NW (ω)
open Vec (ε)

def DataRace : CountersWorld where
  k := 3

  start : Conf 3
    := ## [ω, #0, #0]

  rules : (c : Conf 3) -> List (Bool × Conf 3)
    | out :: cs :: scs :: ε => [
      -- 1
      (out >=# 1 && cs =# 0 && scs =# 0,
          ## [out - #1, #1, #0]),
      -- 2
      (out >=# 1 && cs =# 0,
          ## [out - #1, #0, scs + #1]),
      -- 3
      (cs >=# 1,
          ## [out + #1, cs - #1, scs]),
      -- 4
      (scs >=# 1,
          ## [out + #1, cs, scs - #1])]

  unsafe? : (c : Conf 3) -> Bool
    | _ :: cs :: scs :: ε =>
        cs >=# 1 && scs >=# 1

namespace TestDataRace

def expected : String
:= "\
DataRace (16, 237)
|__[W, 0, 0]
  |
  |__[W, 0, W]
    |
    |__[W, 1, 0]
      |
      |__[W, 0, 0]*
    |
    |__[W, 0, W]*
    |
    |__[W, 0, W]*
"

-- #guard run_min_sc "DataRace" DataRace 3 10 == expected

#guard run_min_sc8 "DataRace" DataRace 3 10 == expected

end TestDataRace
