import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSendResult

/-! Preterminal send failures keep the original fixed ticket pending. The
failed source is the actual final-journal callback, and its history contains
no hidden terminal or allocation event after the retained entry cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations HandshakeSecurity.StagedConservation
open CompletionFirstTerminal

theorem send_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    Appends (CausalJournal.completionOps.send pid skb packet) :=
  Appends.receiptObserved (Appends.focus _ _ _)

theorem mapped_quiet_suffix
    (quiet : HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e)) action)
    (w : World) (history : List CausalJournal.Event) (events : List Completion.Event)
    (grown : (runPrefix action w (history.filterMap CausalJournal.completion?)).2 =
      history.filterMap CausalJournal.completion? ++ events) :
    (history ++ events.map FirstTerminal.encode).filterMap ledgerEvent? = history.filterMap ledgerEvent? := by
  have same := quiet w (history.filterMap CausalJournal.completion?)
  rw [grown,List.filterMap_append] at same
  have empty : events.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = [] :=
    List.append_cancel_left (by simpa only [List.append_nil] using same)
  rw [List.filterMap_append,List.filterMap_map]
  change history.filterMap ledgerEvent? ++ events.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = _
  rw [empty,List.append_nil]

theorem read_ledger_quiet (pid : PeerId) :
    HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e))
      (captureObserved (Completion.access (getPeerMixed pid))) := by
  intro w h
  change (runPrefix (Completion.access (getPeerMixed pid)) w h).2.filterMap _ = _
  exact focusPrefix_other _ _ _ (fun _ => rfl) _ w h

theorem socket_body_ledger_quiet (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) :
    HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e)) (socketBody pid packet peer ipv4) := by
  cases ipv4 <;> exact focusPrefix_other _ _ _ (fun _ => rfl) _

theorem indexed_preterminal_failure
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packet : RunWitness DataPacket)
    (failed : runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
      (.error reason,after))
    (quiet : after.filterMap ledgerEvent? = history.filterMap ledgerEvent?) :
    IndexedStopped context ledger debts reason after := by
  obtain ⟨suffix,grown⟩ := send_appends context.pid skb packet w history
  rw [failed] at grown
  dsimp only at grown
  have empty : suffix.filterMap ledgerEvent? = [] := by
    rw [grown,List.filterMap_append] at quiet
    exact List.append_cancel_left (by simpa only [List.append_nil] using quiet)
  refine ⟨⟨.sending (skb :: rest),.send context.pid skb packet,w,history,before,⟨suffix,grown.symm⟩,?_,quiet,?_⟩⟩
  · change runPrefix (discard (CausalJournal.completionOps.send context.pid skb packet)) w history = _
    rw [discard,runPrefix_bind,failed]
  · rw [grown]
    exact births_quiet_suffix history suffix (fun e member =>
      ledger_quiet_birth e (List.filterMap_eq_nil_iff.mp empty e member))

/-- If the actual peer capture Stops, neither a socket result nor an outer
completed result is emitted. The retained pending cursor is this same call. -/
theorem indexed_read_failure
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packet : RunWitness DataPacket)
    (failed : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.error reason,history.filterMap CausalJournal.completion? ++ events)) :
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
      (.error reason,history ++ events.map FirstTerminal.encode) ∧
    IndexedStopped context ledger debts reason (history ++ events.map FirstTerminal.encode) := by
  have original : runPrefix (Completion.send context.pid skb packet) w
      (history.filterMap CausalJournal.completion?) =
      (.error reason,history.filterMap CausalJournal.completion? ++ events) := by
    rw [send_factor,runPrefix_bind,failed]
  have focused := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w history
    (.error reason) events original
  have observed := SendResult.observed_stopped CausalJournal.Event.sendResult
    (FirstTerminal.focused (Completion.send context.pid skb packet)) context.pid skb packet
    w history _ reason focused
  have quiet := mapped_quiet_suffix (read_ledger_quiet context.pid) w history events
    (congrArg Prod.snd failed)
  exact ⟨observed,indexed_preterminal_failure before packet observed quiet⟩

/-- An actual inner socket Stop has no completed inner or outer result.
The exact read/family prefix and stopped socket body remain visible. -/
theorem indexed_socket_failure
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packet : RunWitness DataPacket) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (failed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events)) :
    let after := (history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history = (.error reason,after) ∧
      IndexedStopped context ledger debts reason after := by
  dsimp only
  have socket : runPrefix (Completion.socket context.pid skb packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
      (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events) := by
    change runPrefix (receiptObserved (socketBody context.pid packet peer ipv4) _) _ _ = _
    rw [runPrefix_receiptObserved,failed]
  have suffixRun : runPrefix
      (Completion.socket context.pid skb packet peer ipv4 >>= afterSocket context.pid packet)
      (familyWorld ipv4 u) ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
      (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events) := by
    rw [runPrefix_bind,socket]
  have focused := (family_send_run context.pid skb packet peer ipv4 w u history readEvents read family).trans
    (focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ (familyWorld ipv4 u)
      (history ++ readEvents.map FirstTerminal.encode) (.error reason) events suffixRun)
  have observed := SendResult.observed_stopped CausalJournal.Event.sendResult
    (FirstTerminal.focused (Completion.send context.pid skb packet)) context.pid skb packet
    w history _ reason focused
  have readQuiet := mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents
    (congrArg Prod.snd read)
  have bodyQuiet := mapped_quiet_suffix (socket_body_ledger_quiet context.pid packet peer ipv4)
    (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) events (congrArg Prod.snd failed)
  exact ⟨observed,indexed_preterminal_failure before packet observed (bodyQuiet.trans readQuiet)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
