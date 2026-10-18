import Leanux.Proofs.WG.Index.SenderIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing
open Queues.RxCredits

theorem sendHandshakeInitiation_hashSlots_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  let D := fun d => HashSlotCoverage d ∧ DeadHashedReserved retired d
  have stable (d e : Device) (same : senderDeviceCell e=senderDeviceCell d) (pre : D d) : D e :=
    ⟨(senderDeviceCell_transports d e retired pid same).1 pre.1,
      (senderDeviceCell_transports d e retired pid same).2.1 pre.2⟩
  have creator : Ensures (createInitiation pid) (fun g => ∀ d,g.dev=some d → D d)
      (fun _ g => ∀ d,g.dev=some d → D d) := by
    intro g a value out b pre run
    have post := createInitiation_hashSlots_retirement retired pid g a value out b
      ⟨fun d hd=>(pre d hd).1,fun d hd=>(pre d hd).2⟩ run
    exact fun d hd=>⟨post.1 d hd,post.2 d hd⟩
  intro g a value out b pre run
  have post := sendInitiation_device_predicate pid D stable creator g a value out b
    (fun d hd=>⟨pre.1 d hd,pre.2 d hd⟩) run
  exact ⟨fun d hd=>(post d hd).1,fun d hd=>(post d hd).2⟩

theorem sendHandshakeInitiation_owner_compatible (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid) (View.HandshakeCompatibleSafe pid)
      (fun _ => View.HandshakeCompatibleSafe pid) := by
  exact sendInitiation_device_predicate pid (HandshakeCompatible pid)
    (fun d e same => (senderDeviceCell_transports d e [] pid same).2.2)
    (createInitiation_owner_compatible pid)

end Leanux.Proofs.WG.Index
