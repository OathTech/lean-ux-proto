import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingSocket

/-! A stopped byte-accounting callback retains the exact native prefix run
from the send entry, and the same settled ledger and cleanup debt. The cut is
constructed from this failed branch, not selected from an unrelated history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal Staged.Obligations StagedTerminalComplete

structure AccountingStop (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (entryWorld : World) (entryHistory : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (reason : Stop) (last : List CausalJournal.Event) where
  result : Int
  world : World
  history : List CausalJournal.Event
  reached : runPrefix (accountingPrefix context.pid skb packet) entryWorld entryHistory =
    (.ok (result,world),history)
  owned : Owned context (.sending rest) history ledger debts world
  complete : Complete history ledger
  failed : runPrefix (FirstTerminal.focused (afterSocket context.pid packet result)) world history =
    (.error reason,last)

def AccountingStop.frontier
    (stopped : AccountingStop context skb rest packet entryWorld entryHistory ledger debts reason last) :
    IndexedFrontier context ledger debts reason last := by
  refine ⟨.sending rest,.accounting context.pid packet stopped.result,stopped.world,stopped.history,
    stopped.owned,?_,?_,?_,?_⟩
  · obtain ⟨suffix,grown⟩ := Appends.focus FirstTerminal.encode CausalJournal.completion?
      (afterSocket context.pid packet stopped.result) stopped.world stopped.history
    change (runPrefix (FirstTerminal.focused (afterSocket context.pid packet stopped.result)) stopped.world stopped.history).2 = _ at grown
    rw [stopped.failed] at grown
    exact ⟨suffix,grown.symm⟩
  · change runPrefix (CompletionBatch.discard (FirstTerminal.focused (afterSocket context.pid packet stopped.result))) stopped.world stopped.history = _
    rw [CompletionBatch.discard,runPrefix_bind,stopped.failed]
  · have quiet := accounting_history_quiet context.pid packet stopped.result stopped.world stopped.history
    simpa only [stopped.failed] using quiet
  · obtain ⟨suffix,grown⟩ := Appends.focus FirstTerminal.encode CausalJournal.completion?
      (afterSocket context.pid packet stopped.result) stopped.world stopped.history
    change (runPrefix (FirstTerminal.focused (afterSocket context.pid packet stopped.result)) stopped.world stopped.history).2 = _ at grown
    have free := focus_birth_free FirstTerminal.encode CausalJournal.completion? completion_encode_births
      (afterSocket context.pid packet stopped.result) stopped.world stopped.history suffix grown
    rw [stopped.failed] at grown
    change last = stopped.history ++ suffix at grown
    exact (congrArg births grown).trans (births_quiet_suffix stopped.history suffix free)

theorem AccountingStop.complete_last
    (stopped : AccountingStop context skb rest packet entryWorld entryHistory ledger debts reason last) :
    Complete last ledger := by
  have kept := Converse.history_preserved stopped.complete (Appends.focus _ _ _)
    (accounting_history_quiet context.pid packet stopped.result) (w := stopped.world)
  simpa only [stopped.failed] using kept

theorem AccountingStop.matched
    (stopped : AccountingStop context skb rest packet entryWorld entryHistory ledger debts reason last) :
    (Cut.indexed stopped.frontier).world = stopped.world ∧
    (Cut.indexed stopped.frontier).before = stopped.history ∧
    (Cut.indexed stopped.frontier).ledger = ledger ∧
    (Cut.indexed stopped.frontier).debts = debts ∧
    (Cut.indexed stopped.frontier).Valid reason last :=
  ⟨rfl,rfl,rfl,rfl,Cut.indexed_valid stopped.frontier stopped.complete_last⟩

theorem AccountingStop.source_failed
    (stopped : AccountingStop context skb rest packet entryWorld entryHistory ledger debts reason last) :
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) entryWorld entryHistory = (.error reason,last) :=
  outer_failed context.pid skb packet stopped.reached stopped.failed

theorem AccountingStop.accounted
    (stopped : AccountingStop context skb rest packet entryWorld entryHistory ledger debts reason last) :
    CompleteCarrier.Accounted last ledger debts
      (⟨.selected,context.pid,context.items⟩ :: context.locals) stopped.world.wg :=
  Converse.indexed_frontier_accounted stopped.frontier stopped.complete_last

theorem socket_accounting_stop
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.ok (ret,v),(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ middle))
    (failed : runPrefix (FirstTerminal.focused (afterSocket context.pid packet ret)) v
      (((history ++ readEvents.map FirstTerminal.encode) ++ middle.map FirstTerminal.encode) ++
        [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,familyWorld ipv4 u,v⟩⟩)]) = (.error reason,last)) :
    let prior := (history ++ readEvents.map FirstTerminal.encode) ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      Nonempty (AccountingStop context skb rest packet w history (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) reason last) := by
  dsimp only
  obtain ⟨chosen,member,head,reached,owned,after⟩ := socket_prefix before complete packetAt ipv4 read family performed
  exact ⟨chosen,member,head,⟨⟨ret,v,_,reached,owned,after,failed⟩⟩⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
