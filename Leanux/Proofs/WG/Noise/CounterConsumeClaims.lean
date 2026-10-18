import Leanux.Proofs.WG.Noise.CounterConsumeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.CounterConsume
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint
variable {α β : Type}

/-- An actual consume occurrence and its same-run internal confirmation,
with the original native witnesses hidden behind the campaign projection. -/
def Occurs (trace : Runner.Trace) (placeholders : Bool) (n id : Nat) (stamp : PacketStamp)
    (observation : ConsumeConfirmation.ConfirmationObservation) : Prop :=
  ∃ (pre post : List RxHistory.Event) (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool),
    (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post ∧
    ConsumeConfirmation.projects r c = observation ∧ r.Valid ∧
    ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
      .ok (((),c.before),c.ambientBefore) ∧
    c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
    ((ConsumeConfirmation.afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
      .ok ((r.run.value,r.run.after),r.run.ambientAfter)

theorem initialized_occurrence (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post) :
    ∃ observation, Occurs trace placeholders n id stamp observation := by
  obtain ⟨a,b,decrypt,out,pid,published,ambient,history,publication,certified⟩ :=
    PublicationRunner.consumed trace placeholders pre post n id stamp r position
  have rv := certified.1.1
  obtain ⟨c,endpoint,confirm,tail,facts⟩ := ConsumeConfirmation.receipt_observation r rv
  exact ⟨ConsumeConfirmation.projects r c,pre,post,r,c,position,rfl,rv,endpoint,confirm,tail⟩

theorem initialized_confirmation_stamped (trace : Runner.Trace) (placeholders : Bool)
    (n id : Nat) (stamp : PacketStamp) (observation : ConsumeConfirmation.ConfirmationObservation)
    (occurs : Occurs trace placeholders n id stamp observation) :
    observation.Valid ∧ observation.Facts ∧ ∃ allocation,
      ConsumeConfirmation.projectedStampAt observation.entry observation.packet.keypair = some allocation ∧
      (observation.confirmed = true → observation.ConfirmedStamp allocation) := by
  obtain ⟨pre,post,r,c,position,rfl,rv,endpoint,confirm,tail⟩ := occurs
  have valid : (ConsumeConfirmation.projects r c).Valid :=
    ⟨r,c,rfl,rv,endpoint,confirm,tail⟩
  obtain ⟨allocation,resident⟩ := initialized_consumed_stamp trace placeholders pre post n id stamp r position
  exact ⟨valid,ConsumeConfirmation.observation_valid_facts _ valid,
    allocation,resident,fun success => ⟨success,resident⟩⟩






end Leanux.Proofs.WG.Noise.CounterConsume
