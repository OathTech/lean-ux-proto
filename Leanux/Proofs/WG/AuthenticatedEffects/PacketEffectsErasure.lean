import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsProjection

/-! Native result and Stop erasure for packet-side effect observation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
open Leanux Leanux.WG Leanux.Proofs.Logged TimerEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {g : Ops (WGPrefix E)}

theorem freshSend_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (freshSendWith g pid) (keepKeyFresh pid) := by
  unfold freshSendWith keepKeyFresh
  repeat' first | with_reducible exact queued_erases h _ _ | timer_effects_erase h

theorem freshReceive_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (freshReceiveWith g pid) (keepKeyFreshRx pid) := by
  rw [freshReceive_factor]
  unfold freshReceiveWith
  rw [← queued_factor]
  simp only [native,id]
  repeat' first | with_reducible exact queued_erases h _ _ | timer_effects_erase h

theorem noKey_erases (h : Ops.Erases g)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    ErasesStatePrefix (noKeyWith g pid packets keypair invalid)
      (Lifetimes.stagedOutNokey pid packets keypair invalid) := by
  rw [noKey_factor]
  unfold noKeyWith
  rw [← queued_factor]
  simp only [native,id]
  repeat' first | with_reducible exact queued_erases h _ _ | timer_effects_erase h

theorem prepare_erases (h : Ops.Erases g) (pid : PeerId) (pkt : RxPacket) :
    ErasesStatePrefix (prepareWith g pid pkt) (Queues.RxCredits.prepareRest pid pkt) := by
  rw [prepare_factor]
  unfold prepareWith
  rw [← freshReceive_factor,← traversal_factor,← dataReceived_factor]
  simp only [native,id]
  repeat' first
    | with_reducible exact freshReceive_erases h _
    | with_reducible exact traversal_erases h _
    | with_reducible exact dataReceived_erases h _
    | timer_effects_erase h

end Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
