import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHistory

/-! The pending-ticket invariant advances at the shared driver's existing
confirmation receipt, before its enclosing receive can stop. Only local source
transport is established here; whole initialized driver closure is separate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins
abbrev Event := Responder.DriverCuts.Event

def Carrier (confirmed : List Nat) (w : WGWorld) : Prop :=
  ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w ∧ Inv confirmed w

def Safe (history : List Event) : Prop := (Responder.DriverCuts.labels history).Nodup

def StateInv (history : List Event) (w : WGWorld) : Prop :=
  Carrier (Responder.DriverCuts.labels history) w

abbrev Observed (action : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => StateInv h w) Safe action

theorem label_matches (kid : KeypairId) (r : WGRunWitness Bool) :
    (label kid r).toList = Responder.confirmedAt r.before kid r.value := by
  cases accepted : r.value <;>
    simp only [label,Responder.confirmedAt,accepted,Bool.false_eq_true,↓reduceIte,Option.toList_none]
  cases device : r.before.dev with
  | none => simp [keypairResidents,Responder.keyCoreAt,device]
  | some d =>
    cases key : d.keypairs[kid]? <;>
      simp [keypairResidents,Responder.keyCoreAt,device,key,Responder.keyCore]

theorem Carrier.initial (net bare : Bool) : Carrier [] (Runner.initialWG net bare) :=
  ⟨ConfiguredMaintenance.configured_initial net bare _ rfl,
    CurrentSlots.initial net bare _ rfl,PendingPromotion.initial net bare⟩

theorem Carrier.session (H1 : H1PendingPromotionEdges) (pid : PeerId)
    (r : WGRunWitness Bool) (hi : Carrier confirmed r.before)
    (valid : r.Valid (beginSession pid)) : Carrier confirmed r.after := by
  refine ⟨?_,?_,PendingPromotion.session H1 pid r hi.2.2 hi.2.1 valid⟩
  · exact (hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame (ConfiguredMaintenance.beginSession_view pid))
      _ _ _ _ _ hi.1 valid
  · exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid)
      _ _ _ _ _ ⟨hi.2.1,hi.1⟩ valid

theorem Carrier.confirmation (H1 : H1PendingPromotionEdges) (pid : PeerId) (kid : KeypairId)
    (r : WGRunWitness Bool) (hi : Carrier confirmed r.before)
    (valid : r.Valid (receivedWithKeypair pid kid)) :
    Carrier (confirmed ++ Responder.confirmedAt r.before kid r.value) r.after := by
  refine ⟨?_,?_,?_⟩
  · exact (hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.receivedWithKeypair_view) pid kid))
      _ _ _ _ _ hi.1 valid
  · exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.receivedWithKeypair_preserves pid kid)
      _ _ _ _ _ hi.2.1 valid
  · simpa only [label_matches] using PendingPromotion.confirmation H1 pid kid r hi.2.2 valid

theorem native (action : WG.M α)
    (frame : ∀ confirmed, Preserves (Carrier confirmed) action) :
    Observed (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2.2.distinct)
  intro h w a value v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (frame _) _ _ _ _ _ hi run

theorem receipt (action : WG.M α) (make : WGRunWitness α → Event)
    (carry : ∀ confirmed r, r.Valid action → Carrier confirmed r.before →
      Carrier (confirmed ++ (make r).labels) r.after) :
    Observed (receiptWGObserved (liftWGPrefix action) make) := by
  intro w a h hi
  have equation := Responder.DriverCuts.receipt_run action make w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : (action.run w).run a with
  | error stop => exact ⟨[],by simp,hi.2.2.distinct,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have after := carry (Responder.DriverCuts.labels h) ⟨value,w,v,a,b⟩ run hi
    have carrier : StateInv (h ++ [make ⟨value,w,v,a,b⟩]) v := by
      simpa only [StateInv,Responder.DriverCuts.labels_append,Responder.DriverCuts.labels_singleton]
        using after
    exact ⟨[make ⟨value,w,v,a,b⟩],rfl,carrier.2.2.distinct,carrier⟩

/-- The native inner promotion is checked and recorded once before any
continuation. The entry invariant is explicit until driver initialization. -/
theorem confirmation_observed (H1 : H1PendingPromotionEdges) (pid : PeerId) (kid : KeypairId) :
    Observed (Responder.DriverCuts.confirmation pid kid) := by
  apply receipt _ (.confirmed pid kid)
  intro confirmed r valid hi
  exact hi.confirmation H1 pid kid r valid

theorem session_observed (H1 : H1PendingPromotionEdges) (pid : PeerId) :
    Observed (Responder.DriverCuts.session pid) := by
  apply receipt _ (.session pid)
  intro confirmed r valid hi
  simpa only [Responder.DriverCuts.Event.labels,List.append_nil] using hi.session H1 pid r valid

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
