import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingPending

/-! Every failed actual send selects a matched pending-entry or post-socket
accounting cut. The case split executes the original capture, family and socket
branches; it does not reinterpret an arbitrary existential frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation

inductive Failed (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | pending (cut : PendingStop context skb rest packet w history ledger debts reason last)
  | accounting (chosen : Binding) (member : chosen ∈ context.bindings) (head : chosen.skb = skb)
      (position : Nat) (sent : Bool)
      (cut : AccountingStop context skb rest packet w history
        (settle [chosen.ticket] (.socket position sent) ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,.socket position sent⟩ :: debts) reason last)

theorem Failed.original (failure : Failed context skb rest packet w history ledger debts reason last) :
    Converse.Stopped context skb ledger debts reason last := by
  cases failure with
  | pending cut => exact Or.inl ⟨⟨cut.frontier⟩,cut.complete_last⟩
  | accounting chosen member head position sent cut =>
    exact Or.inr ⟨chosen,member,head,.socket position sent,True.intro,⟨cut.frontier⟩,cut.complete_last⟩

theorem Failed.source_failed (failure : Failed context skb rest packet w history ledger debts reason last) :
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = (.error reason,last) := by
  cases failure with
  | pending cut => exact cut.failed
  | accounting _ _ _ _ _ cut => exact cut.source_failed

private theorem socket_appends (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Appends (socketBody pid packet peer ipv4) := by
  cases ipv4 <;> exact Appends.focus _ _ _

theorem family_failed
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (failed : runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = (.error reason,last)) :
    Failed context skb rest packet w history ledger debts reason last := by
  let prior := history ++ readEvents.map FirstTerminal.encode
  obtain ⟨events,grown⟩ := socket_appends context.pid packet peer ipv4 (familyWorld ipv4 u)
    (prior.filterMap CausalJournal.completion?)
  cases performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      (prior.filterMap CausalJournal.completion?) with
  | mk outcome socketHistory =>
    rw [performed] at grown
    dsimp only at grown
    cases outcome with
    | error stop =>
      have native : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.error stop,prior.filterMap CausalJournal.completion? ++ events) := by rw [performed,grown]
      have cut := socket_stop before complete packet ipv4 read family native
      rw [cut.failed] at failed
      cases failed
      exact .pending cut
    | ok out =>
      obtain ⟨ret,v⟩ := out
      have native : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
          (prior.filterMap CausalJournal.completion?) =
          (.ok (ret,v),prior.filterMap CausalJournal.completion? ++ events) := by rw [performed,grown]
      obtain ⟨chosen,member,head,reached,owned,paired⟩ := socket_prefix before complete packetAt ipv4 read family native
      let journal := (prior ++ events.map FirstTerminal.encode) ++
        [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,familyWorld ipv4 u,v⟩⟩)]
      cases accounted : runPrefix (FirstTerminal.focused (afterSocket context.pid packet ret)) v journal with
      | mk accountingOutcome after =>
        cases accountingOutcome with
        | error stop =>
          have observed := outer_failed context.pid skb packet reached accounted
          rw [observed] at failed
          cases failed
          exact .accounting chosen member head (prior ++ events.map FirstTerminal.encode).length (ret == 0)
            ⟨ret,v,journal,reached,owned,paired,accounted⟩
        | ok result =>
          have inner : runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history =
              (.ok result,after) := by
            rw [focused_factor,runPrefix_bind,reached]
            exact accounted
          have observed := SendResult.observed_completed CausalJournal.Event.sendResult
            (FirstTerminal.focused (Completion.send context.pid skb packet)) context.pid skb packet
            w result.2 history after result.1 inner
          change runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = _ at observed
          rw [observed] at failed
          cases failed

theorem failed_send
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w)
    (failed : runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = (.error reason,last)) :
    Failed context skb rest packet w history ledger debts reason last := by
  obtain ⟨events,grown⟩ := Appends.captureObserved (Appends.focus _ _ _)
    (a := Completion.access (getPeerMixed context.pid)) w (history.filterMap CausalJournal.completion?)
  cases performed : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) with
  | mk outcome readHistory =>
    rw [performed] at grown
    dsimp only at grown
    cases outcome with
    | error stop =>
      have native : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.error stop,history.filterMap CausalJournal.completion? ++ events) := by rw [performed,grown]
      have cut := read_stop before complete packet native
      rw [cut.failed] at failed
      cases failed
      exact .pending cut
    | ok out =>
      obtain ⟨peer,u⟩ := out
      have read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
          (history.filterMap CausalJournal.completion?) =
          (.ok (peer,u),history.filterMap CausalJournal.completion? ++ events) := by rw [performed,grown]
      by_cases family4 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET
      · exact family_failed before complete packetAt true read family4 failed
      · by_cases family6 : (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6
        · exact family_failed before complete packetAt false read ⟨family4,family6⟩ failed
        · obtain ⟨_,_,_,observed,_,_⟩ := Converse.unsupported_cut before complete packetAt read family4 family6
          rw [observed] at failed
          cases failed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
