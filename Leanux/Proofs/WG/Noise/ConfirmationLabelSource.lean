import Leanux.Proofs.WG.Noise.PendingTicketOptionalClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation PendingTickets

def receiptLabel (r : RxDisposition.ConsumeReceipt) : Option Nat :=
  confirmationInputLabel (Campaign2.snapshot r.run.before r.run.ambientBefore)
    r.peer r.packet.keypair

def eventLabel : RxHistory.Event → Option Nat
  | .consumed _ _ _ r => receiptLabel r
  | _ => none

def confirmationLabels (h : List RxHistory.Event) : List Nat := h.filterMap eventLabel

/-- The event payload and projected observation come from the same completed
consume. This is a source extraction bridge, not a new execution or replay. -/
theorem initialized_event_label (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post) :
    ∃ observation allocation, Occurs trace placeholders n id stamp observation ∧
      receiptLabel r = confirmationInputLabel observation.entry observation.peer observation.packet.keypair ∧
      projectedStampAt observation.entry observation.packet.keypair = some allocation ∧
      receiptLabel r = (if observation.confirmed then some allocation else none) ∧
      (receiptLabel r = some allocation ↔ observation.confirmed = true) := by
  obtain ⟨a,b,decrypt,out,pid,published,ambient,history,publication,certified⟩ :=
    PublicationRunner.consumed trace placeholders pre post n id stamp r position
  have rv := certified.1.1
  obtain ⟨c,endpoint,confirm,tail,_⟩ := receipt_observation r rv
  have occurs : Occurs trace placeholders n id stamp (projects r c) :=
    ⟨pre,post,r,c,position,rfl,rv,endpoint,confirm,tail⟩
  obtain ⟨allocation,resident,label,complete⟩ :=
    initialized_label_complete trace placeholders n id stamp (projects r c) occurs
  exact ⟨projects r c,allocation,occurs,rfl,resident,label,complete⟩

theorem confirmationLabels_at (pre post : List RxHistory.Event)
    (n id : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt) :
    confirmationLabels (pre ++ .consumed n id stamp r :: post) =
      confirmationLabels pre ++ (receiptLabel r).toList ++ confirmationLabels post := by
  simp only [confirmationLabels,List.filterMap_append,List.filterMap_cons,eventLabel]
  cases receiptLabel r <;> simp


end Leanux.Proofs.WG.Noise.CounterConsume
