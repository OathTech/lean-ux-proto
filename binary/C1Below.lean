import C1Interfaces
import C1BelowExit
import C1BelowReady
import C1BelowFlight
import C1BelowInv
import C1BelowStep
import C1BelowUndo
import C1BelowRollback
import C1BelowAlloc
import C1BelowWhole
import C1BelowCover
import C1BelowUndoFinal
import C1BelowPrefixFinal
import C1BelowPrefixBytes
import C1BelowTrunk
import C1BelowSeq
import C1BelowInternal
import C1BelowSplitSegment
import C1BelowSplitReturn
import C1BelowSplitRootReturn

/-! Result C1, work package 3: the paths below the placement. This module is the package's root in
`binary/lakefile.toml`: add modules named `C1Below*.lean` and import them here.
The brief is `binary/Statements/C1/proof/WP3.md`. -/
