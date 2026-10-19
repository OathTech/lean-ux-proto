import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionSequence

/-! Completion reads the current selected cell. The captured receipt is
joined to the same product world, including the actual native packet value;
an unrelated historical read cannot satisfy this callback postcondition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompletionCuts

theorem State.resident (before : State context phase history w)
    (member : skb ∈ phase.active context) :
    ∃ packet, TxDisposition.txPackets w.wg skb = some packet := by
  obtain ⟨_,_,_,_,_,_,_,_,inventory⟩ := before
  exact inventory.localResident skb (by simp [txLocalItems,member])

theorem State.sending_resident (before : State context (.sending (skb :: remaining)) history w) :
    ∃ packet, TxDisposition.txPackets w.wg skb = some packet := by
  have allResident := State.resident (skb := skb) before
  obtain ⟨_,_,_,_,_,suffix,_,_,_⟩ := before
  apply allResident
  obtain ⟨left,same⟩ := suffix
  change skb ∈ context.items
  rw [← same]
  simp [Phase.remaining]

theorem native_packet_total (resident : TxDisposition.txPackets w.wg skb = some packet) :
    (liftWG (getTxSkb skb)).run w = .ok (packet,w) := by
  cases device : w.wg.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    have cell : d.txSkbs[skb]? = some packet := by simpa [TxDisposition.txPackets,device] using resident
    rw [liftWG_run,Packets.getTxSkb_run _ _ d skb packet device cell]
    rfl

theorem packet_checked (context : Context) (skb : SkbId) (remaining : List SkbId) :
    Ensures (State context (.sending (skb :: remaining))) (Stopped context)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun receipt h w => State context (.sending (skb :: remaining)) h w ∧ PacketAt skb receipt w) := by
  intro w history before
  obtain ⟨packet,resident⟩ := before.sending_resident
  have original := native_packet_total resident
  have erases : ErasesPrefix (CausalJournal.completionOps.packet skb) (liftWG (getTxSkb skb)) :=
    focusPrefix_erases _ _ (Completion.access_erases (getTxSkbPrefix_erases skb))
  have appends : Appends (CausalJournal.completionOps.packet skb) := Appends.focus _ _ _
  obtain ⟨suffix,grown⟩ := appends w history
  have run : runPrefix (CausalJournal.completionOps.packet skb) w history =
      (.ok (packet,w),history ++ suffix) := Prod.ext ((erases w history).trans original) grown
  rw [runPrefix_captureObserved,run]
  exact ⟨suffix,rfl,before.append suffix,original,rfl,resident⟩

theorem marker_checked (context : Context) : Holds context (.sending context.items)
    (CausalJournal.completionOps.completion context.pid context.items) := by
  intro w history before
  change ∃ suffix, (runPrefix (focusPrefix _ _ (emitPrefix _)) w history).2 = history ++ suffix ∧ _
  rw [focusPrefix_suffix _ _ _ w history _ [_] (runPrefix_emit _ w _)]
  exact ⟨_,rfl,before.append _⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
