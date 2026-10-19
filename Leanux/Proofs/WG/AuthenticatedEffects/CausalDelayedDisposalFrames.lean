import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedNative

/-! Actual counted purge and reference-release observations retain the live
native timer/work carrier. Their records introduce no new delayed occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open HandshakeSecurity TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000

theorem peer_release (peer : Option PeerId) : StateSafe (CausalJournal.peerRelease peer) := by
  apply observed_native _ _ (focusStatePrefix_erases _ _ (StagedDisposal.release_erases peer))
    (StateAppends.focus _ _ _)
  causal_delayed_native

theorem staged_purge (pid : PeerId) : StateSafe (CausalJournal.stagedPurge pid) := by
  apply observed_native _ _ (focusStatePrefix_erases _ _ (StagedDisposal.purge_erases pid))
    (StateAppends.focus _ _ _)
  unfold purgeStagedPackets
  causal_delayed_native

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
