import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSendFailures

/-! The complete actual send callback advances one selected ticket exactly
once, or retains an exact preterminal/settled Stop frontier. The settlement
ledger and cleanup-debt successor remain explicit in both outcomes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionFirstTerminal CompletionCuts

def SendTerminal : Staged.Obligations.Terminal → Prop
  | .socket _ _ | .sendRefused _ => True
  | _ => False

def SendReturned (context : Context) (skb : SkbId) (rest : List SkbId) (ledger : Ledger)
    (debts : List CleanupDebt) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
    ∃ outcome, SendTerminal outcome ∧ Owned context (.sending rest) history (settle [chosen.ticket] outcome ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) w

def SendStopped (context : Context) (skb : SkbId) (ledger : Ledger) (debts : List CleanupDebt)
    (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  IndexedStopped context ledger debts reason history ∨
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      ∃ outcome, SendTerminal outcome ∧ IndexedStopped context (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) reason history

private theorem body_appends (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Appends (socketBody pid packet peer ipv4) := by
  cases ipv4 <;> exact Appends.focus _ _ _

theorem indexed_family_checked
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer) :
    match (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
    | .error reason => SendStopped context skb ledger debts reason
        (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2
    | .ok (_,v) => SendReturned context skb rest ledger debts
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
      exact Or.inl stopped
    | ok result =>
      obtain ⟨ret,v⟩ := result
      have performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.ok (ret,v),prior.filterMap CausalJournal.completion? ++ events) := by rw [run,grown]
      obtain ⟨chosen,member,head,suffix,extension,safe⟩ :=
        indexed_family_accounting before packetAt ipv4 read family performed
      obtain ⟨tail,_,outer⟩ := indexed_observed_after_settlement context skb rest packet w history _ _ _
        ⟨suffix,extension⟩ safe
      cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
      | error reason =>
        rw [ended] at outer
        exact Or.inr ⟨chosen,member,head,.socket (prior ++ events.map FirstTerminal.encode).length (ret == 0),True.intro,outer⟩
      | ok result =>
        obtain ⟨sent,after⟩ := result
        rw [ended] at outer
        exact ⟨chosen,member,head,.socket (prior ++ events.map FirstTerminal.encode).length (ret == 0),True.intro,outer⟩

/-- This actual send callback needs no supplied read/socket-success premise.
Every normal path settles exactly the selected head once; a Stop keeps either
its original pending ledger or its actual first-terminal successor ledger. -/
theorem indexed_send_checked (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (ledger : Ledger) (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context (.sending (skb :: rest)) h ledger debts w ∧ PacketAt skb packet w)
      (SendStopped context skb ledger debts) (CausalJournal.completionOps.send context.pid skb packet)
      (fun _ => SendReturned context skb rest ledger debts) := by
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
      exact Or.inl stopped
    | ok result =>
      obtain ⟨peer,u⟩ := result
      have read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.ok (peer,u),history.filterMap CausalJournal.completion? ++ events) := by rw [run,extension]
      by_cases family4 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET
      · have checked := indexed_family_checked before.1 before.2 true read family4
        cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
        | error reason => simpa only [ended] using checked
        | ok out => obtain ⟨sent,after⟩ := out; simpa only [ended] using checked
      · by_cases family6 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6
        · have checked := indexed_family_checked before.1 before.2 false read ⟨family4,family6⟩
          cases ended : (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
          | error reason => simpa only [ended] using checked
          | ok out => obtain ⟨sent,after⟩ := out; simpa only [ended] using checked
        · obtain ⟨chosen,member,head,_,observed,after⟩ :=
            indexed_unsupported_advanced before.1 before.2 read family4 family6
          rw [observed]
          exact ⟨chosen,member,head,.sendRefused (history ++ events.map FirstTerminal.encode).length,True.intro,after⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
