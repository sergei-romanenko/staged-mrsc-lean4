-- This module serves as the root of the `SMRSC` library.
-- Import modules here that should be built as part of the library.
import SMRSC.Basic

import SMRSC.Util
import SMRSC.AbstractSc
import SMRSC.AlmostFullRel
import SMRSC.BarWhistles
import SMRSC.Graphs
import SMRSC.BigStepSc
import SMRSC.Cographs
import SMRSC.Statistics

-- Tests

import SMRSC.Test.Cartesian
import SMRSC.Test.Graphs
import SMRSC.Test.BigStepSc

-- An instantiation of the model for counter systems

import SMRSC.Counters
import SMRSC.Protocols.Synapse
