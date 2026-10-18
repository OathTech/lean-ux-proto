import Leanux.Proofs.WG.HandshakeSecurity.ResponderJointConsumer
import Leanux.Proofs.WG.HandshakeSecurity.ResponderPollLeafFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem access_rule (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (base : List Nat) (erases : ErasesPrefix g a)
    (preserves : ∀ confirmed, Preserves (fun w : World => Native confirmed w.wg) a) :
    PrefixPreserves (State base) (Checks base) (RxJoint.access g) :=
  quiet _ a base (RxJoint.access_appends g) (RxJoint.access_erases erases)
    (fun w h => focusPrefix_other RxJoint.Event.access RxJoint.accessEvent consumer (fun _ => rfl) g w h)
    preserves

theorem native_access (g : MixedM α) (a : WG.M α)
    (base : List Nat) (erases : ErasesStatePrefix g a)
    (preserves : ∀ confirmed, Preserves (Native confirmed) a) :
    PrefixPreserves (State base) (Checks base) (RxJoint.access (liftWGObserver g)) :=
  access_rule _ _ base (liftWGObserver_erases erases)
    (fun confirmed => PublicationPoll.native_product _ a (preserves confirmed))

theorem lift_rule (a : Leanux.M α) (base : List Nat)
    (preserves : ∀ confirmed, Preserves (fun w : World => Native confirmed w.wg) a) :
    PrefixPreserves (State base) (Checks base) (liftPrefix a) :=
  quiet _ a base (Appends.lift a) (erasesPrefix_lift a) (HistoryFrame.lift _ a) preserves

theorem emit_rule (e : RxJoint.Event) (base : List Nat) (he : consumer e = none) :
    PrefixPreserves (State base) (Checks base) (emitPrefix e) := by
  intro w h hi
  have safe := hi.2.snoc (checked_quiet he)
  refine ⟨[e], rfl, safe, ?_, safe⟩
  change Native (base ++ labels (h ++ [e])) w.wg
  rw [labels_append]
  have noLabel : labels [e] = [] := by simp [labels, label, he]
  simpa only [noLabel, List.append_nil] using hi.1

theorem receipt_rule (a : RxJoint.Obs α) (event : RunWitness α → RxJoint.Event)
    (base : List Nat) (ha : PrefixPreserves (State base) (Checks base) a)
    (he : ∀ r, consumer (event r) = none) :
    PrefixPreserves (State base) (Checks base) (receiptObserved a event) := by
  unfold receiptObserved
  exact ha.captureObserved.bind (fun r => (emit_rule _ base (he r)).bind
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _))

theorem read_native (id : SkbId) (confirmed : List Nat) :
    Preserves (Native confirmed) (getRxSkb id) := by
  unfold getRxSkb
  exact native_skb _ confirmed

theorem free_native (id : SkbId) (confirmed : List Nat) :
    Preserves (Native confirmed) (freeRxSkb id) := by
  unfold freeRxSkb
  exact native_skb _ confirmed

theorem capture_rule (id : SkbId) (base : List Nat) :
    PrefixPreserves (State base) (Checks base) (RxJoint.capture id) := by
  intro w h hi
  rw [RxJoint.capture_run]
  cases hr : (liftWG (getRxSkb id)).run w with
  | error e => exact ⟨[], by simp, hi.2, True.intro⟩
  | ok out =>
    rcases out with ⟨pkt, v⟩
    have frame := (hoare_iff_run _ _ _).mp
      (PublicationPoll.native_product _ _ (read_native id _)) w pkt v hi.1 hr
    let e := RxJoint.Event.access (.packet (.read (.inr id) (packetStamp w.wg id)))
    have safe : Checks base (h ++ [e]) := hi.2.snoc True.intro
    refine ⟨[e], rfl, safe, ?_, safe⟩
    change Native (base ++ labels (h ++ [e])) v.wg
    rw [labels_append]
    simpa only [show labels [e] = [] from rfl, List.append_nil] using frame

theorem drop_rule (pid n id : Nat) (stamp : PacketStamp) (base : List Nat) :
    PrefixPreserves (State base) (Checks base) (RxJoint.drop pid n id stamp) := by
  unfold RxJoint.drop
  exact (native_access _ _ base (rxDropPeekedPrefix_erases pid)
    (drop_native pid)).bind (fun _ => emit_rule _ base rfl)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
