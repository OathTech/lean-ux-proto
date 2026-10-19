import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFreeLoop

/-! The real send loop retains a sequence of first-terminal settlements on
one explicit ledger. Its cleanup debts remain attached to this selected batch;
a stopped inner send retains the same concrete pending or settled cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts

inductive SendSettlements (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    Ledger → List CleanupDebt → Prop where
  | start : SendSettlements context initial original initial original
  | settle (prior : SendSettlements context initial original ledger debts)
      (binding : Binding) (member : binding ∈ context.bindings)
      (outcome : Staged.Obligations.Terminal) (terminal : SendTerminal outcome)
      (pending : binding.pending ledger)
      (transition : Staged.Obligations.Step ledger (settle [binding.ticket] outcome ledger)) :
      SendSettlements context initial original (settle [binding.ticket] outcome ledger)
        (⟨binding.ticket,binding.position,binding.ordinal,outcome⟩ :: debts)

theorem SendSettlements.step (trace : SendSettlements context initial original ledger debts) :
    Staged.Obligations.Step initial ledger := by
  induction trace with
  | start => exact Step.refl _
  | settle _ _ _ _ _ _ transition ih => exact ih.trans transition

private theorem SendSettlements.next (trace : SendSettlements context initial original ledger debts)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (chosen : Binding) (member : chosen ∈ context.bindings) (head : chosen.skb = skb)
    (outcome : Staged.Obligations.Terminal) (terminal : SendTerminal outcome) :
    SendSettlements context initial original (Staged.Obligations.settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) := by
  have pending := (before.cursor.assigned chosen member).1 (by simp [head])
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.entry.core.physical,before.entry.core.valid⟩
  exact trace.settle chosen member outcome terminal pending (support.settle pending outcome).1

def Sending (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ ledger debts, SendSettlements context initial original ledger debts ∧
    Owned context (.sending remaining) history ledger debts w ∧
    LocalDebts context context.items debts

def SendingStopped (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  ∃ ledger debts, SendSettlements context initial original ledger debts ∧
    IndexedStopped context ledger debts reason history

theorem Sending.start (before : Owned context (.sending remaining) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) :
    Sending context ledger debts remaining history w :=
  ⟨ledger,debts,.start,before,localDebts⟩

private theorem sending_packet (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) :
    Ensures (Sending context initial original (skb :: rest)) (SendingStopped context initial original)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun packet h w => Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before
  obtain ⟨suffix,grown,checked⟩ := indexed_packet_checked context skb rest ledger debts w history owned
  refine ⟨suffix,grown,?_⟩
  cases result : (runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w history).1 with
  | error reason => exact ⟨ledger,debts,trace,by simpa only [result] using checked⟩
  | ok out =>
    obtain ⟨packet,v⟩ := out
    rw [result] at checked
    exact ⟨⟨ledger,debts,trace,checked.1,localDebts⟩,checked.2⟩

private theorem sending_branch (decision : Decision) (value : Bool)
    (context : Context) (initial : Ledger) (original : List CleanupDebt) (rest : List SkbId) :
    Ensures (Sending context initial original rest) (SendingStopped context initial original)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => Sending context initial original rest) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before
  rw [branch_run]
  exact ⟨[],by simp,ledger,debts,trace,owned.sameWG rfl,localDebts⟩

private theorem sending_send (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (packet : RunWitness DataPacket) :
    Ensures (fun h w => Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w)
      (SendingStopped context initial original) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => Sending context initial original rest) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before.1
  obtain ⟨suffix,grown,checked⟩ := indexed_send_checked context skb rest packet ledger debts w history
    ⟨owned,before.2⟩
  refine ⟨suffix,grown,?_⟩
  cases result : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
  | error reason =>
    rw [result] at checked
    rcases checked with pending | ⟨chosen,member,head,outcome,terminal,settled⟩
    · exact ⟨ledger,debts,trace,pending⟩
    · exact ⟨_,_,trace.next owned chosen member head outcome terminal,settled⟩
  | ok out =>
    obtain ⟨sent,v⟩ := out
    rw [result] at checked
    obtain ⟨chosen,member,head,outcome,terminal,after⟩ := checked
    exact ⟨_,_,trace.next owned chosen member head outcome terminal,after,localDebts.settle member outcome⟩

private theorem sending_and (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (rest : List SkbId) (first second : Bool) :
    Ensures (Sending context initial original rest) (SendingStopped context initial original)
      (TxDisposition.andObs (CausalJournal.completionOps.step (branch .doneSendOk first))
        (CausalJournal.completionOps.step (branch .doneNotKeepalive second)))
      (fun _ => Sending context initial original rest) := by
  unfold TxDisposition.andObs
  apply Ensures.bind (sending_branch _ _ _ _ _ _)
  intro value
  cases value
  · exact Ensures.pure (fun _ _ before => before)
  · exact sending_branch _ _ _ _ _ _

theorem indexed_iteration_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (dataSent : Bool) :
    Ensures (Sending context initial original (skb :: rest)) (SendingStopped context initial original)
      (iteration CausalJournal.completionOps context.pid skb dataSent)
      (fun _ => Sending context initial original rest) := by
  unfold iteration
  apply Ensures.bind (sending_packet context initial original skb rest)
  intro packet
  apply Ensures.bind (Q := fun _ h w =>
    Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w)
  · intro w history before
    obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before.1
    rw [branch_run]
    exact ⟨[],by simp,⟨ledger,debts,trace,owned.sameWG rfl,localDebts⟩,before.2.sameWG rfl⟩
  intro _
  apply Ensures.bind (sending_send context initial original skb rest packet)
  intro sent
  apply Ensures.bind (sending_and context initial original rest sent
    (!(packet.value.bytes.length == MESSAGE_DATA_LEN_0)))
  intro value
  cases value <;> exact Ensures.pure (fun _ _ before => before)

/-- No send-success or native-read premise is supplied. Every iteration uses
the packet captured from this same world and keeps the exact settlement chain. -/
theorem indexed_sendLoop_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (dataSent : Bool) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      (sendLoop CausalJournal.completionOps context.pid remaining dataSent)
      (fun _ => Sending context initial original []) := by
  induction remaining generalizing dataSent with
  | nil => exact Ensures.pure (fun _ _ before => before)
  | cons skb rest ih =>
    unfold sendLoop
    exact Ensures.bind (indexed_iteration_checked context initial original skb rest dataSent) ih

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
