import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteResult

/-! The actual send callback pairs source ownership and historical terminal
completeness on one explicit successor ledger. Every source branch retains
that pairing, including failures before or after the first terminal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionFirstTerminal CompletionCuts StagedTerminalComplete

def Returned (context : Context) (skb : SkbId) (rest : List SkbId) (ledger : Ledger)
    (debts : List CleanupDebt) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
    ∃ outcome, SendTerminal outcome ∧ Owned context (.sending rest) history (settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) w ∧
      Complete history (settle [chosen.ticket] outcome ledger)

def Stopped (context : Context) (skb : SkbId) (ledger : Ledger) (debts : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  (IndexedStopped context ledger debts reason history ∧ Complete history ledger) ∨
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      ∃ outcome, SendTerminal outcome ∧ IndexedStopped context (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) reason history ∧
        Complete history (settle [chosen.ticket] outcome ledger)

private theorem body_appends (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Appends (socketBody pid packet peer ipv4) := by
  cases ipv4 <;> exact Appends.focus _ _ _

theorem family_checked
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
    (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer) :
    match (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
    | .error reason => Stopped context skb ledger debts reason
        (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2
    | .ok (_,v) => Returned context skb rest ledger debts
        (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2 v := by
  let prior := history ++ readEvents.map FirstTerminal.encode
  obtain ⟨events,grown⟩ := body_appends context.pid packet peer ipv4 (familyWorld ipv4 u)
    (prior.filterMap CausalJournal.completion?)
  cases run : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      (prior.filterMap CausalJournal.completion?) with
  | mk result journal =>
    rw [run] at grown
    dsimp only at grown
    cases result with
    | error reason =>
      have failed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.error reason,prior.filterMap CausalJournal.completion? ++ events) := by rw [run,grown]
      obtain ⟨observed,stopped⟩ := indexed_socket_failure before packet ipv4 read family failed
      rw [observed]
      exact Or.inl ⟨stopped,socket_failure_complete complete read failed⟩
    | ok result =>
      obtain ⟨ret,v⟩ := result
      have performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.ok (ret,v),prior.filterMap CausalJournal.completion? ++ events) := by rw [run,grown]
      obtain ⟨chosen,member,head,completeAfter,suffix,extension,safe⟩ :=
        family_accounting before complete packetAt ipv4 read family performed
      obtain ⟨tail,_,outer⟩ := indexed_observed_after_settlement context skb rest packet w history _ _ _
        ⟨suffix,extension⟩ safe
      have paired := observed_complete (supported_entry read family) completeAfter
      cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
      | error reason =>
        rw [ended] at outer
        exact Or.inr ⟨chosen,member,head,.socket (prior ++ events.map FirstTerminal.encode).length (ret == 0),True.intro,outer,paired⟩
      | ok result =>
        obtain ⟨sent,after⟩ := result
        rw [ended] at outer
        exact ⟨chosen,member,head,.socket (prior ++ events.map FirstTerminal.encode).length (ret == 0),True.intro,outer,paired⟩

/-- This actual send callback needs no supplied read/socket-success premise.
Every normal path settles exactly the selected head once; a Stop keeps either
its original pending ledger or its actual first-terminal successor ledger. -/
theorem send_checked (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (ledger : Ledger) (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context (.sending (skb :: rest)) h ledger debts w ∧ Complete h ledger ∧ PacketAt skb packet w)
      (Stopped context skb ledger debts) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => Returned context skb rest ledger debts) := by
  intro w history before
  obtain ⟨suffix,grown⟩ := send_appends context.pid skb packet w history
  refine ⟨suffix,grown,?_⟩
  obtain ⟨events,extension⟩ := Appends.captureObserved (Appends.focus _ _ _)
    (a := Completion.access (getPeerMixed context.pid)) w (history.filterMap CausalJournal.completion?)
  cases run : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) with
  | mk result journal =>
    rw [run] at extension
    dsimp only at extension
    cases result with
    | error reason =>
      have failed : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.error reason,history.filterMap CausalJournal.completion? ++ events) := by rw [run,extension]
      obtain ⟨observed,stopped⟩ := indexed_read_failure before.1 packet failed
      rw [observed]
      exact Or.inl ⟨stopped,read_failure_complete before.2.1 failed⟩
    | ok result =>
      obtain ⟨peer,u⟩ := result
      have read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.ok (peer,u),history.filterMap CausalJournal.completion? ++ events) := by rw [run,extension]
      by_cases family4 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET
      · have checked := family_checked before.1 before.2.1 before.2.2 true read family4
        cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
        | error reason => simpa only [ended] using checked
        | ok out => obtain ⟨sent,after⟩ := out; simpa only [ended] using checked
      · by_cases family6 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6
        · have checked := family_checked before.1 before.2.1 before.2.2 false read ⟨family4,family6⟩
          cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
          | error reason => simpa only [ended] using checked
          | ok out => obtain ⟨sent,after⟩ := out; simpa only [ended] using checked
        · obtain ⟨chosen,member,head,observed,after,complete⟩ :=
            unsupported_cut before.1 before.2.1 before.2.2 read family4 family6
          rw [observed]
          exact ⟨chosen,member,head,.sendRefused (history ++ events.map FirstTerminal.encode).length,True.intro,after,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
