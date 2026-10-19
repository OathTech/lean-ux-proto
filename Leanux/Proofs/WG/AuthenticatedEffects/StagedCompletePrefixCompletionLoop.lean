import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionSend

/-! Prefix safety follows the actual packet/send loop while retaining its
source settlement trace, indexed cursor and growing cleanup-debt list. The
postcondition does not replace those witnesses with an existential account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {Safe : List CausalJournal.Event → Prop}

theorem Checked.pure (post : ∀ h w, P h w → Q value h w) :
    Checked P Safe stopped (pure value) Q :=
  CompletionCuts.Ensures.pure (fun h w before => ⟨post h w before.1,before.2⟩)

private theorem trace_next {initial : Ledger} (trace : SendSettlements context initial original ledger debts)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (chosen : Binding) (member : chosen ∈ context.bindings) (head : chosen.skb = skb)
    (outcome : Staged.Obligations.Terminal) (terminal : SendTerminal outcome) :
    SendSettlements context initial original (settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) := by
  have pending := (before.cursor.assigned chosen member).1 (by simp [head])
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.entry.core.physical,before.entry.core.valid⟩
  exact trace.settle chosen member outcome terminal pending (support.settle pending outcome).1

private theorem sending_packet (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original (skb :: rest)) Safe (Converse.SendingStopped context initial original)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun receipt h w => Converse.Sending context initial original (skb :: rest) h w ∧ PacketAt skb receipt w) := by
  intro w h before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1
  obtain ⟨suffix,grown,result⟩ := packet context skb rest ledger debts accountSafe w h ⟨⟨owned,complete⟩,before.2⟩
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix (captureObserved (CausalJournal.completionOps.packet skb)) w h).1 with
  | error reason =>
    rw [run] at result
    exact ⟨⟨ledger,debts,trace,result.1.1,result.1.2⟩,result.2⟩
  | ok out =>
    obtain ⟨receipt,v⟩ := out
    rw [run] at result
    exact ⟨⟨⟨ledger,debts,trace,result.1.1,localDebts,result.1.2.2⟩,result.1.2.1⟩,result.2⟩

private theorem sending_send (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (packet : RunWitness DataPacket) (accountSafe : AccountSafe Safe) :
    Checked (fun h w => Converse.Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w)
      Safe (Converse.SendingStopped context initial original) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => Converse.Sending context initial original rest) := by
  intro w h before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1.1
  obtain ⟨suffix,grown,result⟩ := send context skb rest packet ledger debts accountSafe w h
    ⟨⟨owned,complete,before.1.2⟩,before.2⟩
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w h).1 with
  | error reason =>
    rw [run] at result
    refine ⟨?_,result.2⟩
    rcases result.1 with pending | ⟨chosen,member,head,outcome,terminal,settled,paired⟩
    · exact ⟨ledger,debts,trace,pending.1,pending.2⟩
    · exact ⟨_,_,trace_next trace owned chosen member head outcome terminal,settled,paired⟩
  | ok out =>
    obtain ⟨sent,v⟩ := out
    rw [run] at result
    obtain ⟨chosen,member,head,outcome,terminal,after,paired⟩ := result.1
    exact ⟨⟨_,_,trace_next trace owned chosen member head outcome terminal,after,
      localDebts.settle member outcome,paired⟩,result.2⟩

theorem sending_branch (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (decision : Decision) (value : Bool) :
    Checked (Converse.Sending context initial original remaining) Safe (Converse.SendingStopped context initial original)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => Converse.Sending context initial original remaining) := by
  intro w h before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1
  rw [branch_run]
  exact ⟨[],by simp,⟨ledger,debts,trace,owned.sameWG rfl,localDebts,complete⟩,before.2⟩

private theorem sending_and (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (rest : List SkbId) (first second : Bool) :
    Checked (Converse.Sending context initial original rest) Safe (Converse.SendingStopped context initial original)
      (TxDisposition.andObs (CausalJournal.completionOps.step (branch .doneSendOk first))
        (CausalJournal.completionOps.step (branch .doneNotKeepalive second)))
      (fun _ => Converse.Sending context initial original rest) := by
  unfold TxDisposition.andObs
  apply Checked.bind (sending_branch _ _ _ _ _ _)
  intro value
  cases value
  · exact Checked.pure (fun _ _ before => before)
  · exact sending_branch _ _ _ _ _ _

theorem iteration (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (dataSent : Bool) (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original (skb :: rest)) Safe (Converse.SendingStopped context initial original)
      (CompletionBatch.iteration CausalJournal.completionOps context.pid skb dataSent)
      (fun _ => Converse.Sending context initial original rest) := by
  unfold CompletionBatch.iteration
  apply Checked.bind (sending_packet context initial original skb rest accountSafe)
  intro packet
  apply Checked.bind (Q := fun _ h w =>
    Converse.Sending context initial original (skb :: rest) h w ∧ PacketAt skb packet w)
  · intro w h before
    obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before.1.1
    rw [branch_run]
    exact ⟨[],by simp,⟨⟨ledger,debts,trace,owned.sameWG rfl,localDebts,complete⟩,
      before.1.2.sameWG rfl⟩,before.2⟩
  intro _
  apply Checked.bind (sending_send context initial original skb rest packet accountSafe)
  intro sent
  apply Checked.bind (sending_and context initial original rest sent
    (!(packet.value.bytes.length == MESSAGE_DATA_LEN_0)))
  intro value
  cases value <;> exact Checked.pure (fun _ _ before => before)

theorem send_loop (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (dataSent : Bool) (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original remaining) Safe (Converse.SendingStopped context initial original)
      (sendLoop CausalJournal.completionOps context.pid remaining dataSent)
      (fun _ => Converse.Sending context initial original []) := by
  induction remaining generalizing dataSent with
  | nil => exact Checked.pure (fun _ _ before => before)
  | cons skb rest ih =>
    unfold sendLoop
    exact Checked.bind (iteration context initial original skb rest dataSent accountSafe) ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
