import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontBody
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontErrors

/-! Refused front invocations have one native error-counter charge, separate
from the earlier counted disposal of any staged packets. Segment count does
not multiply the invocation charge. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open CausalJournal
set_option pp.structureInstances false

theorem invocation_charge (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w v : WGWorld) (a b : Ambient) (h hist : List Event) (result : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front family addr packets mtu) w a h =
      (.ok ((result,v),b),hist)) :
    HandshakeSecurity.StagedConservation.Front.FrontResult
      (HandshakeSecurity.StagedConservation.Front.errors w) result v := by
  have erased := HandshakeSecurity.StagedConservation.Front.observed_erases
    Event.transmitInput Event.stagedDisposal stagedDisposal?
    (fun input r => Event.old (.routed input.family input.address input.packets input.mtu r))
    ⟨family,addr,packets,mtu⟩ w a h
  change (runWGPrefix (CausalJournal.front family addr packets mtu) w a h).1 = _ at erased
  rw [run] at erased
  exact (hoare_iff_run_ambient _ _ _).mp
    (HandshakeSecurity.StagedConservation.Front.front_charge family addr packets mtu _)
    w a result v b rfl erased.symm

theorem refused_once (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w v : WGWorld) (a b : Ambient) (h hist : List Event) (code : Int)
    (run : runWGPrefix (CausalJournal.front family addr packets mtu) w a h =
      (.ok ((.error code,v),b),hist)) :
    (code = -EPROTONOSUPPORT ∨ code = -ENOKEY ∨ code = -EDESTADDRREQ ∨ code = -ENOMEM) ∧
    v.dev.map Device.txErrors = (w.dev.map Device.txErrors).map (· + 1) :=
  invocation_charge family addr packets mtu w v a b h hist (.error code) run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
