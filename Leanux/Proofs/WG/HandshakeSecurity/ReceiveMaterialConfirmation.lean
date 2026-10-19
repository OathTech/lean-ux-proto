import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialExecution
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder

/-! The actual shared confirmation hook emits the allocation certificate
before its caller can stage a send or stop. The conditioned entry remains
explicit here and is discharged only by the native accepted-packet path. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

def ConfirmationInput (pid : PeerId) (kid : KeypairId)
    (h : List Journal.Event) (w : World) : Prop :=
  Replay.ConfirmationInput Journal.origin? Journal.replay? Journal.Event.replay pid kid h w ∧
    KeyBounds w.wg ∧ Confirmation.Safe h

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    StatePrefixEnsures
      (fun h w a => ConfirmationInput pid kid h (NativeAdapter.world w a)) Safe
      (Journal.confirmation pid kid) (fun _ h w _ => Carrier h w) := by
  intro w a h hi
  have equation := ConfirmationTransportOrder.confirmation_run Journal.Event.responder Journal.responder?
    pid kid w a h
  change runWGPrefix (Journal.confirmation pid kid) w a h = _ at equation
  unfold runWGPrefix runStatePrefix at equation
  rw [equation]
  have before : Replay.Inv Journal.origin? Journal.replay? h (NativeAdapter.world w a) := by
    obtain ⟨pkt,_,_,accepted⟩ := hi.1
    exact accepted.1
  cases run : ((receivedWithKeypair pid kid).run w).run a with
  | error err => exact ⟨[],by simp,⟨before.2,hi.2.2⟩,trivial⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : WGRunWitness Bool := ⟨value,w,v,a,b⟩
    let event : Journal.Event := .responder (.confirmed pid kid r)
    have safe : Safe (h ++ [event]) :=
      ⟨before.2.quiet rfl,Confirmation.append_confirmation hi.2.2 hi.1 r rfl run⟩
    have kept := (hoare_iff_run_ambient _ _ _).mp (bounded_confirmation pid kid)
      w a value v b ⟨before.1,hi.2.1⟩ run
    refine ⟨[event],rfl,safe,?_,safe⟩
    simpa only [event,Journal.origin?,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Option.toList_none,List.nil_append,List.append_nil] using kept

theorem confirmation_product (pid : PeerId) (kid : KeypairId) :
    PrefixEnsures (ConfirmationInput pid kid) Safe (liftWGObserver (Journal.confirmation pid kid))
      (fun _ h w => Carrier h w.wg) := by
  apply (confirmation pid kid).liftWGObserver.consequence
  · intro h w hi
    obtain ⟨pkt,peer,key,accepted⟩ := hi.1
    exact ⟨⟨pkt,peer,key,accepted⟩,hi.2⟩
  · intro _ _ _ hi
    exact hi

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
