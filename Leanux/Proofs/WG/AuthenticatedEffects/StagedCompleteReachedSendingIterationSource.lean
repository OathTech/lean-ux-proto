import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingCases
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSendLoop

/-! Fixed source prefix from an iteration entry to the actual send callback.
Packet capture is total from this same owned resident cell; native branch
bookkeeping changes only the recorded ambient choices. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

def iterationPrefix (skb : SkbId) : PrefixM CausalJournal.Event (RunWitness DataPacket) := do
  let packet ← captureObserved (CausalJournal.completionOps.packet skb)
  _ ← CausalJournal.completionOps.step (branch .doneSkbIterate true)
  pure packet

def afterSend (packet : RunWitness DataPacket) (dataSent sent : Bool) : PrefixM CausalJournal.Event Bool := do
  if ← TxDisposition.andObs (CausalJournal.completionOps.step (branch .doneSendOk sent))
      (CausalJournal.completionOps.step (branch .doneNotKeepalive
        (!(packet.value.bytes.length == MESSAGE_DATA_LEN_0)))) then return true
  return dataSent

def afterPacket (pid : PeerId) (skb : SkbId) (dataSent : Bool) (packet : RunWitness DataPacket) :
    PrefixM CausalJournal.Event Bool := do
  let sent ← CausalJournal.completionOps.send pid skb packet
  afterSend packet dataSent sent

theorem iteration_factor (pid : PeerId) (skb : SkbId) (dataSent : Bool) :
    iteration CausalJournal.completionOps pid skb dataSent =
      (iterationPrefix skb >>= afterPacket pid skb dataSent) := by
  simp only [iteration,iterationPrefix,afterPacket,afterSend,bind_assoc,pure_bind]

theorem after_send_total (packet : RunWitness DataPacket) (dataSent sent : Bool)
    (w : World) (history : List CausalJournal.Event) :
    ∃ value v, runPrefix (afterSend packet dataSent sent) w history = (.ok (value,v),history) ∧ v.wg = w.wg := by
  unfold afterSend TxDisposition.andObs
  simp only [runPrefix_bind,branch_run]
  cases sent with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,runPrefix_pure]
    exact ⟨dataSent,_,rfl,rfl⟩
  | true =>
    cases keepalive : (packet.value.bytes.length == MESSAGE_DATA_LEN_0) with
    | false =>
      simp only [↓reduceIte,Bool.not_false,branch_run,runPrefix_pure]
      exact ⟨true,_,rfl,rfl⟩
    | true =>
      simp only [↓reduceIte,Bool.not_true,branch_run,Bool.false_eq_true,runPrefix_pure]
      exact ⟨dataSent,_,rfl,rfl⟩

theorem iteration_entry
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) :
    ∃ packet u middle,
      runPrefix (iterationPrefix skb) w history = (.ok (packet,u),middle) ∧
      Owned context (.sending (skb :: rest)) middle ledger debts u ∧
      Complete middle ledger ∧ PacketAt skb packet u := by
  obtain ⟨packet,resident⟩ := before.state.sending_resident
  have native := native_packet_total resident
  have erases : ErasesPrefix (CausalJournal.completionOps.packet skb) (liftWG (getTxSkb skb)) :=
    focusPrefix_erases _ _ (Completion.access_erases (getTxSkbPrefix_erases skb))
  obtain ⟨suffix,grown⟩ := Appends.focus (a := Completion.access (getTxSkbPrefix skb))
    FirstTerminal.encode CausalJournal.completion? w history
  have read : runPrefix (CausalJournal.completionOps.packet skb) w history =
      (.ok (packet,w),history ++ suffix) := Prod.ext ((erases w history).trans native) grown
  have captured : runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w history =
      (.ok (⟨packet,w,w⟩,w),history ++ suffix) := by rw [runPrefix_captureObserved,read]; rfl
  obtain ⟨_,_,checked⟩ := indexed_packet_checked context skb rest ledger debts w history before
  rw [captured] at checked
  have paired : Complete (history ++ suffix) ledger := by
    have same := Converse.focused_access_complete complete (getTxSkbPrefix skb) w
    change Complete (runPrefix (CausalJournal.completionOps.packet skb) w history).2 ledger at same
    simpa only [read] using same
  refine ⟨⟨packet,w,w⟩,{w with ambient := CounterWindow.record w.ambient .doneSkbIterate true},
    history ++ suffix,?_,checked.1.sameWG rfl,paired,checked.2.sameWG rfl⟩
  unfold iterationPrefix
  rw [runPrefix_bind,captured]
  simp only [runPrefix_bind,branch_run,runPrefix_pure]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
