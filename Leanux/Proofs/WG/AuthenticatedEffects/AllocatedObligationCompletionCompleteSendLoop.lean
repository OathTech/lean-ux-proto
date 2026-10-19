import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSend

/-! The real send loop carries the historical terminal converse together
with its exact source settlement chain, selected cursor and cleanup debts.
No generic ledger-step implication is used to recover completeness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts StagedTerminalComplete

theorem focused_access_complete (complete : Complete history ledger) (action : MixedM α) (w : World) :
    Complete (runPrefix (FirstTerminal.focused (Completion.access action)) w history).2 ledger := by
  have appends : Appends (Completion.access action) := Appends.focus _ _ _
  obtain ⟨events,grown⟩ := appends w
    (history.filterMap CausalJournal.completion?)
  have actual : runPrefix (Completion.access action) w (history.filterMap CausalJournal.completion?) =
      ((runPrefix (Completion.access action) w (history.filterMap CausalJournal.completion?)).1,
        history.filterMap CausalJournal.completion? ++ events) := Prod.ext rfl grown
  have focused := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w history _ events actual
  rw [focused]
  exact complete.append_quiet (completion_events_quiet (no_socket_suffix (access_no_socket action) actual))

private theorem trace_next (trace : SendSettlements context initial original ledger debts)
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
    LocalDebts context context.items debts ∧ Complete history ledger

def SendingStopped (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  ∃ ledger debts, SendSettlements context initial original ledger debts ∧
    IndexedStopped context ledger debts reason history ∧ Complete history ledger

theorem Sending.start (before : Owned context (.sending remaining) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) (complete : Complete history ledger) :
    Sending context ledger debts remaining history w :=
  ⟨ledger,debts,.start,before,localDebts,complete⟩

private theorem sending_packet (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) :
    Ensures (Sending context initial original (skb :: rest)) (SendingStopped context initial original)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun packet h w => Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  obtain ⟨suffix,grown,checked⟩ := indexed_packet_checked context skb rest ledger debts w history owned
  have paired : Complete (runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w history).2 ledger :=
    focused_access_complete complete (getTxSkbPrefix skb) w
  refine ⟨suffix,grown,?_⟩
  cases result : (runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w history).1 with
  | error reason => exact ⟨ledger,debts,trace,(by simpa only [result] using checked),paired⟩
  | ok out =>
    obtain ⟨packet,v⟩ := out
    rw [result] at checked
    exact ⟨⟨ledger,debts,trace,checked.1,localDebts,paired⟩,checked.2⟩

private theorem sending_branch (decision : Decision) (value : Bool)
    (context : Context) (initial : Ledger) (original : List CleanupDebt) (rest : List SkbId) :
    Ensures (Sending context initial original rest) (SendingStopped context initial original)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => Sending context initial original rest) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  rw [branch_run]
  exact ⟨[],by simp,ledger,debts,trace,owned.sameWG rfl,localDebts,complete⟩

private theorem sending_send (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (packet : RunWitness DataPacket) :
    Ensures (fun h w => Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w)
      (SendingStopped context initial original) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => Sending context initial original rest) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1
  obtain ⟨suffix,grown,checked⟩ := send_checked context skb rest packet ledger debts w history
    ⟨owned,complete,before.2⟩
  refine ⟨suffix,grown,?_⟩
  cases result : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
  | error reason =>
    rw [result] at checked
    rcases checked with pending | ⟨chosen,member,head,outcome,terminal,settled,paired⟩
    · exact ⟨ledger,debts,trace,pending.1,pending.2⟩
    · exact ⟨_,_,trace_next trace owned chosen member head outcome terminal,settled,paired⟩
  | ok out =>
    obtain ⟨sent,v⟩ := out
    rw [result] at checked
    obtain ⟨chosen,member,head,outcome,terminal,after,paired⟩ := checked
    exact ⟨_,_,trace_next trace owned chosen member head outcome terminal,after,localDebts.settle member outcome,paired⟩

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

theorem iteration_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
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
    obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1
    rw [branch_run]
    exact ⟨[],by simp,⟨ledger,debts,trace,owned.sameWG rfl,localDebts,complete⟩,before.2.sameWG rfl⟩
  intro _
  apply Ensures.bind (sending_send context initial original skb rest packet)
  intro sent
  apply Ensures.bind (sending_and context initial original rest sent
    (!(packet.value.bytes.length == MESSAGE_DATA_LEN_0)))
  intro value
  cases value <;> exact Ensures.pure (fun _ _ before => before)

/-- No send-success or native-read premise is supplied. Every iteration uses
the packet captured from this same world and keeps the exact settlement chain. -/
theorem sendLoop_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (dataSent : Bool) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      (sendLoop CausalJournal.completionOps context.pid remaining dataSent)
      (fun _ => Sending context initial original []) := by
  induction remaining generalizing dataSent with
  | nil => exact Ensures.pure (fun _ _ before => before)
  | cons skb rest ih =>
    unfold sendLoop
    exact Ensures.bind (iteration_checked context initial original skb rest dataSent) ih

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
