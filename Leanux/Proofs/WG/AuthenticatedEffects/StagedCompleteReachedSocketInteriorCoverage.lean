import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorPending
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorTunnel

/-! Exhaustive actual socket outcomes and their original send-entry bridge.
The branch reaching a socket retains the same captured peer, family guards,
packet binding and caller ledger. Unsupported families have no inner socket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open CompletionFirstTerminal

/-- Every actual socket invocation either stops in the original front, or
reaches a total result/receipt interval for one original allocated ticket. -/
theorem socket_coverage
    (before : Owned context (.sending (skb :: rest)) history ledger debts entry)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet entry)
    (peerValid : peer.Valid (liftWG (getPeer context.pid))) (ipv4 : Bool) :
    (∃ reason events,
      runPrefix (socketFront context.pid packet peer ipv4) entry (history.filterMap CausalJournal.completion?) =
        (.error reason,history.filterMap CausalJournal.completion? ++ events) ∧
      runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4)) entry history =
        (.error reason,history ++ events.map FirstTerminal.encode)) ∨
    (∃ result frontWorld events,
      Nonempty (Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events)) := by
  have appends : Appends (socketFront context.pid packet peer ipv4) := Appends.focus _ _ _
  obtain ⟨events,grown⟩ := appends entry (history.filterMap CausalJournal.completion?)
  cases front : runPrefix (socketFront context.pid packet peer ipv4) entry (history.filterMap CausalJournal.completion?) with
  | mk out journal =>
    rw [front] at grown
    dsimp only at grown
    subst journal
    cases out with
    | error reason =>
      refine Or.inl ⟨reason,events,rfl,?_⟩
      apply focusPrefix_suffix FirstTerminal.encode CausalJournal.completion?
      rw [socket_cases,front]
    | ok value =>
      rcases value with ⟨result,frontWorld⟩
      exact Or.inr ⟨result,frontWorld,events,awaiting before complete packetAt peerValid front⟩

theorem from_send_entry
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (front : runPrefix (socketFront context.pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.ok (result,frontWorld),(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ events)) :
    Nonempty (Awaiting context skb rest packet peer ipv4 (history ++ readEvents.map FirstTerminal.encode)
      ledger debts (familyWorld ipv4 u) result frontWorld events) := by
  have readWorld := FirstTerminal.peer_cut_world context.pid w u peer _ _ read
  have same : (familyWorld ipv4 u).wg = w.wg := by cases ipv4 <;> exact readWorld
  have kept := (before.append (readEvents.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births e)).sameWG same
  have paired := Converse.extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents (congrArg Prod.snd read))
  exact awaiting kept paired (packetAt.sameWG same) (peer_cut_facts context.pid w u peer _ _ read).1 front

variable {context : Context} {skb : SkbId} {rest : List SkbId}
  {packet : RunWitness DataPacket} {peer : RunWitness Peer} {ipv4 : Bool}
  {history : List CausalJournal.Event} {ledger : Ledger} {debts : List CleanupDebt}
  {w u frontWorld : World} {result : Except Int SentDatagram} {events readEvents : List Completion.Event}

theorem send_accounting_prefix
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (point : Awaiting context skb rest packet peer ipv4 (history ++ readEvents.map FirstTerminal.encode)
      ledger debts (familyWorld ipv4 u) result frontWorld events) :
    runPrefix (Sending.accountingPrefix context.pid skb packet) w history =
      (.ok (resultCode result,resultWorld frontWorld result),point.prior ++
        [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 (familyWorld ipv4 u) result frontWorld))]) := by
  rw [Sending.prefix_family context.pid skb packet peer ipv4 w u history readEvents read family]
  exact point.source

theorem send_continuation
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (point : Awaiting context skb rest packet peer ipv4 (history ++ readEvents.map FirstTerminal.encode)
      ledger debts (familyWorld ipv4 u) result frontWorld events) :
    runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history =
      runPrefix (FirstTerminal.focused (afterSocket context.pid packet (resultCode result)))
        (resultWorld frontWorld result) (point.prior ++
          [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 (familyWorld ipv4 u) result frontWorld))]) := by
  rw [Sending.focused_factor,runPrefix_bind,send_accounting_prefix read family point]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
