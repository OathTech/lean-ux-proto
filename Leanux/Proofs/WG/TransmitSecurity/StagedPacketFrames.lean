import Leanux.Proofs.WG.TransmitSecurity.StagedNativeTactics

/-! Packet store and replay-counter operations retain staged peer queues. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem skb (action : SkbM α) : Preserves (Inv h) (liftSkb action) := by
  apply hoare_liftSkb
  intro w d packets before device
  apply before.retains
  · simp only [Packets.epoch,device,Option.map_some]
  · intro pid cell found
    simpa only [stagedAt,device,Option.bind_some] using found

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Inv h) (counterValidate kid nonce) := by
  unfold counterValidate
  simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head setKeypair; exact write_key _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_origin_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
