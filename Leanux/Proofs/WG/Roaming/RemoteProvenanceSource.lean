import Leanux.Proofs.WG.Roaming.RemoteProvenanceBridge
import Leanux.Proofs.WG.Roaming.ConsumptionDestinationClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

namespace ReceiveStepRemote
theorem matches_facts (r : RunWitness Bool) (q : Observation) (matched : Matches r q) :
    q.Facts := by
  obtain ⟨entry,finish,value,d,ring,device,rest⟩ := matched
  refine ⟨d,?_,?_⟩
  · rw [entry]
    exact device
  · cases selected : q.call with
    | none =>
      rw [selected] at rest
      dsimp only at rest ⊢
      obtain ⟨queue,returned,after⟩ := rest
      refine ⟨value.trans returned,congrArg Prod.fst queue,?_⟩
      rw [entry,finish,after]
      rfl
    | some call =>
      rw [selected] at rest
      dsimp only at rest ⊢
      obtain ⟨queue,returned,callFinish,run,callEntry,callAfter,after⟩ := rest
      refine ⟨value.trans returned,congrArg Prod.fst queue,?_,?_,?_⟩
      · rw [callEntry,entry]
        exact dequeue_remotes r.before ring
      · rw [finish,after,callAfter]
        exact decrement_remotes callFinish
      · rw [callEntry,callAfter]
        exact Product.observedHandshakeRemotes_facts call.message call.source
          (Campaign2.Product.snapshot (dequeued r.before ring))
          (dequeued r.before ring) call.receipt callFinish rfl run
end ReceiveStepRemote

namespace RemoteProvenance
theorem origin_at_cause (trace : Runner.Trace) (placeholders : Bool)
    (events : List RemoteDriver.Event)
    (exactRx : events.filterMap RemoteDriver.rxEvent = ConfirmationOrder.history trace placeholders)
    (safe : RemoteDriver.Safe events) (event : RemoteDriver.Event)
    (before after : List RemoteDriver.Event) (position : events = before ++ event :: after)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (cause : RemoteDriver.Cause event pid remote)
    (target : List RemoteDriver.Event) (targetMember : event ∈ target) :
    ∃ origin : Origin, Matches trace placeholders target origin ∧ origin.Facts pid remote ∧
      (match origin with
       | .data q _ => q.position = (before.filterMap RemoteDriver.rxEvent).length
       | _ => True) := by
  have member : event ∈ events := by rw [position]; simp
  cases event with
  | endpoint run =>
    have valid : run.Valid := safe _ member
    refine ⟨.configuration run.projects,⟨run,targetMember,valid,rfl⟩,?_,True.intro⟩
    exact ⟨cause.1,cause.2.1,cause.2.2,run.effect valid⟩
  | receive run =>
    obtain ⟨q,matched,origin⟩ := cause
    have valid : run.Valid (liftWG receiveStep) := safe _ member
    exact ⟨.handshake q,⟨run,targetMember,valid,matched⟩,
      ⟨ReceiveStepRemote.matches_facts run q matched,origin⟩,True.intro⟩
  | birth receipt => cases cause
  | rx event =>
    cases event with
    | consumed occurrence skb stamp receipt =>
      let pre := before.filterMap RemoteDriver.rxEvent
      let post := after.filterMap RemoteDriver.rxEvent
      have rxPosition : ConfirmationOrder.history trace placeholders =
          pre ++ .consumed occurrence skb stamp receipt :: post := by
        rw [← exactRx,position,List.filterMap_append,List.filterMap_cons]
        rfl
      obtain ⟨q,occurs,qPosition,_,_,_,matched⟩ :=
        ConfirmationOrder.initialized_event trace placeholders pre post occurrence skb stamp receipt rxPosition
      obtain ⟨authentication,authenticated,facts⟩ :=
        consumption_authenticated trace placeholders q occurs
      have atPosition : ConfirmationOrder.Matches q.position occurrence skb stamp receipt q := by
        simpa only [qPosition] using matched
      have peer : q.observation.peer = receipt.peer := by
        obtain ⟨_,c,allocation,_,_,rfl⟩ := matched
        rfl
      have endpoint : q.observation.endpoint = receipt.endpoint := by
        obtain ⟨_,c,allocation,_,_,rfl⟩ := matched
        rfl
      refine ⟨.data q authentication,⟨occurs,authenticated,
        occurrence,skb,stamp,receipt,targetMember,atPosition⟩,?_,qPosition⟩
      exact ⟨peer.trans cause.1,(congrArg destination endpoint).trans cause.2.1,
        facts,consumption_final_remotes trace placeholders q occurs⟩
    | _ => cases cause

theorem origin_of_cause_in (trace : Runner.Trace) (placeholders : Bool)
    (events : List RemoteDriver.Event)
    (exactRx : events.filterMap RemoteDriver.rxEvent = ConfirmationOrder.history trace placeholders)
    (safe : RemoteDriver.Safe events) (event : RemoteDriver.Event) (member : event ∈ events)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (cause : RemoteDriver.Cause event pid remote)
    (target : List RemoteDriver.Event) (targetMember : event ∈ target) :
    ∃ origin : Origin, Matches trace placeholders target origin ∧ origin.Facts pid remote := by
  obtain ⟨before,after,position⟩ := List.append_of_mem member
  obtain ⟨origin,matched,facts,_⟩ := origin_at_cause trace placeholders events
    exactRx safe event before after position pid remote cause target targetMember
  exact ⟨origin,matched,facts⟩

theorem origin_of_cause (trace : Runner.Trace) (placeholders : Bool)
    (events : List RemoteDriver.Event)
    (exactRx : events.filterMap RemoteDriver.rxEvent = ConfirmationOrder.history trace placeholders)
    (safe : RemoteDriver.Safe events) (event : RemoteDriver.Event) (member : event ∈ events)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (cause : RemoteDriver.Cause event pid remote) :
    ∃ origin : Origin, Matches trace placeholders events origin ∧ origin.Facts pid remote :=
  origin_of_cause_in trace placeholders events exactRx safe event member pid remote cause events member

theorem covered_origins (trace : Runner.Trace) (placeholders : Bool)
    (entry final : RemoteMap) (events : List RemoteDriver.Event)
    (exactRx : events.filterMap RemoteDriver.rxEvent = ConfirmationOrder.history trace placeholders)
    (safe : RemoteDriver.Safe events)
    (covered : RemoteCovered entry RemoteDriver.Cause events final) :
    ∀ pid remote, final pid = some remote →
      entry pid = some remote ∨
      ∃ origin : Origin, Matches trace placeholders events origin ∧ origin.Facts pid remote := by
  intro pid remote present
  rcases covered pid remote present with initial | ⟨event,member,cause⟩
  · exact Or.inl initial
  · exact Or.inr (origin_of_cause trace placeholders events exactRx safe event member pid remote cause)

end RemoteProvenance
end Leanux.Proofs.WG.Roaming
