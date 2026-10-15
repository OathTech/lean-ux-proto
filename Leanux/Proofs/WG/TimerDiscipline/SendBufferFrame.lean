import Leanux.Proofs.WG.TimerDiscipline.SendSocketFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The socket send preserves the retry projection while updating its own
endpoint-cache and accounting fields. The projection contains fields not in
campaign 1's keypair snapshot. -/
theorem sendBufferToPeer_spec_initiation_variant (pid : PeerId) (bytes : List UInt8)
    (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have ha := keypairAllocation_kernel_spec_sendBuffer_variant
    (fun k => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v)
  have hg := getPeer_initiationView pid v
  have hp := setPeer_initiationView pid v
  have h4 := fun e => send4_initiationView pid e bytes HANDSHAKE_DSCP true v
  have h6 := fun e => send6_initiationView pid e bytes HANDSHAKE_DSCP true v
  mvcgen [sendBufferToPeer, branch, invariant, ha, hg, hp, h4, h6]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt]

end Leanux.Proofs.WG.TimerDiscipline
