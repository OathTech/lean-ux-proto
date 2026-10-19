import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionSocket

/-! Preterminal failures use the unchanged pending ledger. An unsupported
family settles once at the outer result; a supported outer result preserves
the already chosen socket terminal, including a false result for errno. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation
variable {Safe : List CausalJournal.Event → Prop} {packet : RunWitness DataPacket}

theorem read_failure_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
    (failed : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.error reason,history.filterMap CausalJournal.completion? ++ events)) :
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
      (.error reason,history ++ events.map FirstTerminal.encode) ∧
    IndexedStopped context ledger debts reason (history ++ events.map FirstTerminal.encode) ∧
    Complete (history ++ events.map FirstTerminal.encode) ledger ∧
    Cuts Safe history (events.map FirstTerminal.encode) := by
  obtain ⟨observed,stopped⟩ := indexed_read_failure before packet failed
  exact ⟨observed,stopped,Converse.read_failure_complete complete failed,
    quiet_cuts accountSafe before complete
      (mapped_quiet_suffix (read_ledger_quiet context.pid) w history events (congrArg Prod.snd failed))⟩

theorem socket_failure_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (ipv4 : Bool)
    (read : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (failed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4)
      (familyWorld ipv4 u) ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.error reason,(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events)) :
    runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
      (.error reason,(history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode) ∧
    IndexedStopped context ledger debts reason
      ((history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode) ∧
    Complete ((history ++ readEvents.map FirstTerminal.encode) ++ events.map FirstTerminal.encode) ledger ∧
    Cuts Safe history (readEvents.map FirstTerminal.encode ++ events.map FirstTerminal.encode) := by
  obtain ⟨observed,stopped⟩ := indexed_socket_failure before packet ipv4 read family failed
  have readQuiet := mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents (congrArg Prod.snd read)
  have socketQuiet := mapped_quiet_suffix (socket_body_ledger_quiet context.pid packet peer ipv4)
    (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) events (congrArg Prod.snd failed)
  refine ⟨observed,stopped,Converse.socket_failure_complete complete read failed,?_⟩
  apply quiet_cuts accountSafe before complete
  simpa only [List.append_assoc] using socketQuiet.trans readQuiet

theorem unsupported_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w)
    (read : runPrefix (captureObserved (TransmitSecurity.Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨context.pid,skb,packet,⟨false,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.sendRefused prior.length
    let journal := prior ++ [CausalJournal.Event.sendResult receipt]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
        (.ok (false,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v ∧
      Complete journal (settle [chosen.ticket] outcome ledger) ∧
      Cuts Safe history (middle.map FirstTerminal.encode ++ [CausalJournal.Event.sendResult receipt]) := by
  dsimp only
  obtain ⟨chosen,member,head,source,owned,settled⟩ := Converse.unsupported_cut before complete packetAt read not4 not6
  have prior := quiet_cuts accountSafe before complete
    (mapped_quiet_suffix (read_ledger_quiet context.pid) w history middle (congrArg Prod.snd read))
  exact ⟨chosen,member,head,source,owned,settled,
    prior.append (Cuts.singleton prior.last (owned_safe accountSafe owned settled))⟩

theorem supported_result_cuts (accountSafe : AccountSafe Safe)
    (supported : endpointFamily w.wg pid = AF_INET ∨ endpointFamily w.wg pid = AF_INET6)
    (performed : runPrefix (FirstTerminal.focused (TransmitSecurity.Completion.send pid skb packet)) w history =
      (.ok (sent,v),history ++ suffix))
    (before : Owned context phase (history ++ suffix) ledger debts v)
    (complete : Complete (history ++ suffix) ledger) (cuts : Cuts Safe history suffix) :
    let event := CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨sent,w,v⟩⟩
    runPrefix (CausalJournal.completionOps.send pid skb packet) w history =
      (.ok (sent,v),(history ++ suffix) ++ [event]) ∧
    Owned context phase ((history ++ suffix) ++ [event]) ledger debts v ∧
    Complete ((history ++ suffix) ++ [event]) ledger ∧
    Cuts Safe history (suffix ++ [event]) := by
  dsimp only
  have source : CausalJournal.completionOps.send pid skb packet =
      SendResult.observed CausalJournal.Event.sendResult
        (FirstTerminal.focused (TransmitSecurity.Completion.send pid skb packet)) pid skb packet := rfl
  have owned := before.append [CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨sent,w,v⟩⟩]
    (by intro e member; cases List.mem_singleton.mp member; rfl)
  have paired := complete.append_quiet
    (suffix := [CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨sent,w,v⟩⟩]) (by
      intro e member
      cases List.mem_singleton.mp member
      exact supported_result_quiet supported)
  refine ⟨?_,owned,paired,cuts.append (Cuts.singleton cuts.last (owned_safe accountSafe owned paired))⟩
  simp only [source,SendResult.observed,runPrefix_receiptObserved,performed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
