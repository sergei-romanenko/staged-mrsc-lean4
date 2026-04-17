--
-- SMRSC.Test.Cartesian
--

import Batteries
import Aesop

import SMRSC.Util

#guard cartesian (α := Nat) [] == [[]]
#guard cartesian [[], [10, 20]] == []
#guard cartesian [[1, 2], []] == []
#guard cartesian [[1, 2]] == [[1], [2]]
#guard cartesian [[1], [10, 20]] == [[1, 10], [1, 20]]
#guard cartesian [[1, 2], [10, 20, 30], [100, 200]] == [
        [1, 10, 100], [1, 10, 200],
        [1, 20, 100], [1, 20, 200],
        [1, 30, 100], [1, 30, 200],
        [2, 10, 100], [2, 10, 200],
        [2, 20, 100], [2, 20, 200],
        [2, 30, 100], [2, 30, 200]]
