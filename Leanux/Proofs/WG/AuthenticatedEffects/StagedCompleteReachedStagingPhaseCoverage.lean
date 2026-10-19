import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseAllocation

/-! Source-local semantic staging certificates: native take, key borrowing,
checked nonce traversal, ordered restoration, partial allocation aliases and
the actual create child. Each point retains its literal original continuation.

This module does not yet prove Covers for the complete stagingShape or
keepaliveShape. Remaining composition includes the outer selection receipt,
strict peer acquisition, rejected-prefix/queued suffix and keepalive birth
phases. Shared key repayment, peer release and queued-initiation primitive
interiors remain separate named source contracts. No initialized or global
native-cut coverage follows merely from the endpoint carrier. -/
