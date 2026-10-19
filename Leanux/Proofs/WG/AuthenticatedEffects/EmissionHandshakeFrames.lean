import Leanux.Proofs.WG.AuthenticatedEffects.EmissionNativeFrames

/-! Noise message construction has no socket append. Its original index and
peer writes remain in the source; only the emitted-message caller sends. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem create_initiation (pid : PeerId) : SameView WGWorld.sent (createInitiation pid) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant,unsupported,IndexOwner.peerDeref,IndexOwner.peerWord]
  repeat' consumer_sent_step initial

theorem create_response (pid : PeerId) : SameView WGWorld.sent (createResponse pid) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant,unsupported,IndexOwner.peerDeref,IndexOwner.peerWord]
  repeat' consumer_sent_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
