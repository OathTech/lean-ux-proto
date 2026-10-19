import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontErrors

/-! The early-error count is attached to the original native invocation.
A supplied GSO list does not multiply this charge by its packet count. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets

private theorem tail_zero (pid : PeerId) (r : WGRunWitness Int)
    (run : r.Valid (txTail pid)) : r.value = 0 := by
  unfold WGRunWitness.Valid txTail at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,_,_,_,run⟩ := run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,_,_,_,run⟩ := run
  exact (congrArg (fun p => p.1.1) (Except.ok.inj run)).symm

/-- Every nonzero return of the original transmit invocation is a named
front refusal with exactly one device error charge, independent of GSO size.
Successful splice, and a later stopped send tail, are separate outcomes. -/
theorem xmit_refusal (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (r : WGRunWitness Int) (run : r.Valid (wgXmit family addr packets mtu))
    (refused : r.value ≠ 0) :
    (r.value = -EPROTONOSUPPORT ∨ r.value = -ENOKEY ∨
      r.value = -EDESTADDRREQ ∨ r.value = -ENOMEM) ∧
    errors r.after = (errors r.before).map (· + 1) ∧
    ((txFront family addr packets mtu).run r.before).run r.ambientBefore =
      .ok ((.error r.value,r.after),r.ambientAfter) := by
  unfold WGRunWitness.Valid at run
  rw [wgXmit_front_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨selected,middle,clock,front,tail⟩ := run
  cases selected with
  | error code =>
    have output := Except.ok.inj tail
    have value : code = r.value := congrArg (fun p => p.1.1) output
    have world : middle = r.after := congrArg (fun p => p.1.2) output
    have ambient : clock = r.ambientAfter := congrArg (fun p => p.2) output
    subst code middle clock
    have counted := (hoare_iff_run_ambient _ _ _).mp
      (front_charge family addr packets mtu (errors r.before))
      r.before r.ambientBefore (.error r.value) r.after r.ambientAfter rfl front
    exact ⟨counted.1,counted.2,front⟩
  | ok pid => exact (refused (tail_zero pid ⟨r.value,middle,r.after,clock,r.ambientAfter⟩ tail)).elim

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
