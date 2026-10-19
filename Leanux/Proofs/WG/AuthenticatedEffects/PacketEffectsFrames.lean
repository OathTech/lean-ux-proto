import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsErasure

/-! Packet-side maintenance retains the current lexical scope while observing
native timer and work effects; neutral callbacks equal the original lift. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
open Leanux Leanux.WG Leanux.Proofs.Logged TimerEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {g : Ops (WGPrefix E)}

theorem freshSend_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (freshSendWith g pid) := by
  unfold freshSendWith
  repeat' first | with_reducible exact queued_frame ρ h _ _ | timer_effects_frame h ρ

theorem freshReceive_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (freshReceiveWith g pid) := by
  unfold freshReceiveWith
  repeat' first | with_reducible exact queued_frame ρ h _ _ | timer_effects_frame h ρ

theorem noKey_frame (ρ : E → Option F) (h : Ops.Frames ρ g)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateHistoryFrame ρ (noKeyWith g pid packets keypair invalid) := by
  unfold noKeyWith
  repeat' first | with_reducible exact queued_frame ρ h _ _ | timer_effects_frame h ρ

theorem prepare_frame (ρ : E → Option F) (h : Ops.Frames ρ g)
    (pid : PeerId) (pkt : RxPacket) : StateHistoryFrame ρ (prepareWith g pid pkt) := by
  unfold prepareWith
  repeat' first
    | with_reducible exact freshReceive_frame ρ h _
    | with_reducible exact traversal_frame ρ h _
    | with_reducible exact dataReceived_frame ρ h _
    | timer_effects_frame h ρ

theorem freshSend_lifted (pid : PeerId) :
    freshSendWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (keepKeyFresh pid) :=
  eq_native_lift (freshSend_erases lifted_erases pid) (freshSend_frame some (lifted_frames some) pid)

theorem freshReceive_lifted (pid : PeerId) :
    freshReceiveWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (keepKeyFreshRx pid) :=
  eq_native_lift (freshReceive_erases lifted_erases pid) (freshReceive_frame some (lifted_frames some) pid)

theorem noKey_lifted (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    noKeyWith (lifted : Ops (WGPrefix E)) pid packets keypair invalid =
      liftWGPrefix (Lifetimes.stagedOutNokey pid packets keypair invalid) :=
  eq_native_lift (noKey_erases lifted_erases pid packets keypair invalid)
    (noKey_frame some (lifted_frames some) pid packets keypair invalid)

theorem prepare_lifted (pid : PeerId) (pkt : RxPacket) :
    prepareWith (lifted : Ops (WGPrefix E)) pid pkt = liftWGPrefix (Queues.RxCredits.prepareRest pid pkt) :=
  eq_native_lift (prepare_erases lifted_erases pid pkt) (prepare_frame some (lifted_frames some) pid pkt)

end Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
