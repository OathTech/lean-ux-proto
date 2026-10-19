import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingAccounting

/-! A preterminal failure retains the actual send entry and its pending
head ticket. The source run and quiet ledger suffix are derived from the real
peer-read or socket-body arm; no terminal receipt is invented on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal Staged.Obligations StagedTerminalComplete

structure PendingStop (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (reason : Stop) (last : List CausalJournal.Event) : Prop where
  owned : Owned context (.sending (skb :: rest)) history ledger debts w
  complete : Complete history ledger
  failed : runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = (.error reason,last)
  quiet : last.filterMap ledgerEvent? = history.filterMap ledgerEvent?

def PendingStop.frontier
    (stopped : PendingStop context skb rest packet w history ledger debts reason last) :
    IndexedFrontier context ledger debts reason last := by
  refine ⟨.sending (skb :: rest),.send context.pid skb packet,w,history,stopped.owned,?_,?_,stopped.quiet,?_⟩
  · obtain ⟨suffix,grown⟩ := send_appends context.pid skb packet w history
    rw [stopped.failed] at grown
    exact ⟨suffix,grown.symm⟩
  · change runPrefix (CompletionBatch.discard (CausalJournal.completionOps.send context.pid skb packet)) w history = _
    rw [CompletionBatch.discard,runPrefix_bind,stopped.failed]
  · obtain ⟨suffix,grown⟩ := send_appends context.pid skb packet w history
    rw [stopped.failed] at grown
    change last = history ++ suffix at grown
    have quiet := stopped.quiet
    have empty : suffix.filterMap ledgerEvent? = [] := by
      rw [grown,List.filterMap_append] at quiet
      exact List.append_cancel_left (by simpa only [List.append_nil] using quiet)
    rw [grown]
    exact births_quiet_suffix history suffix (fun event member =>
      ledger_quiet_birth event (List.filterMap_eq_nil_iff.mp empty event member))

theorem PendingStop.complete_last
    (stopped : PendingStop context skb rest packet w history ledger debts reason last) :
    Complete last ledger := by
  obtain ⟨suffix,grown⟩ := send_appends context.pid skb packet w history
  rw [stopped.failed] at grown
  exact Converse.extension stopped.complete grown stopped.quiet

theorem PendingStop.matched
    (stopped : PendingStop context skb rest packet w history ledger debts reason last) :
    (Cut.indexed stopped.frontier).world = w ∧ (Cut.indexed stopped.frontier).before = history ∧
    (Cut.indexed stopped.frontier).ledger = ledger ∧ (Cut.indexed stopped.frontier).debts = debts ∧
    (Cut.indexed stopped.frontier).Valid reason last :=
  ⟨rfl,rfl,rfl,rfl,Cut.indexed_valid stopped.frontier stopped.complete_last⟩

theorem read_stop
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packet : RunWitness DataPacket)
    (failed : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.error reason,history.filterMap CausalJournal.completion? ++ events)) :
    PendingStop context skb rest packet w history ledger debts reason
      (history ++ events.map FirstTerminal.encode) := by
  obtain ⟨observed,_⟩ := indexed_read_failure before packet failed
  exact ⟨before,complete,observed,mapped_quiet_suffix (read_ledger_quiet context.pid) w history events
    (congrArg Prod.snd failed)⟩

theorem socket_stop
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packet : RunWitness DataPacket) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (failed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events)) :
    PendingStop context skb rest packet w history ledger debts reason
      ((history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode) := by
  obtain ⟨observed,_⟩ := indexed_socket_failure before packet ipv4 read family failed
  have readQuiet := mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents
    (congrArg Prod.snd read)
  have bodyQuiet := mapped_quiet_suffix (socket_body_ledger_quiet context.pid packet peer ipv4)
    (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) events (congrArg Prod.snd failed)
  exact ⟨before,complete,observed,bodyQuiet.trans readQuiet⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
