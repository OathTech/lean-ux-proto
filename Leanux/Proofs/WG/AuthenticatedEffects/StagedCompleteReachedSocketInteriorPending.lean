import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorObserved

/-! One original allocated head ticket awaits its actual socket receipt.
The result interval keeps the real append and the total receipt suffix; it
is not represented as a new pending account after an external send. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open CompletionFirstTerminal

structure Awaiting (context : Context) (skb : SkbId) (rest : List SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool)
    (history : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt)
    (entry : World) (result : Except Int SentDatagram) (frontWorld : World)
    (events : List Completion.Event) where
  before : Owned context (.sending (skb :: rest)) history ledger debts entry
  complete : Complete history ledger
  packetAt : PacketAt skb packet entry
  peerValid : peer.Valid (liftWG (getPeer context.pid))
  front : runPrefix (socketFront context.pid packet peer ipv4) entry
    (history.filterMap CausalJournal.completion?) =
      (.ok (result,frontWorld),history.filterMap CausalJournal.completion? ++ events)
  chosen : Binding
  member : chosen ∈ context.bindings
  head : chosen.skb = skb
  after : Owned context (.sending rest)
    ((history ++ events.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld))])
    (settle [chosen.ticket] (.socket (history ++ events.map FirstTerminal.encode).length (resultCode result == 0)) ledger)
    (⟨chosen.ticket,chosen.position,chosen.ordinal,
      .socket (history ++ events.map FirstTerminal.encode).length (resultCode result == 0)⟩ :: debts)
    (resultWorld frontWorld result)
  afterComplete : Complete
    ((history ++ events.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld))])
    (settle [chosen.ticket] (.socket (history ++ events.map FirstTerminal.encode).length (resultCode result == 0)) ledger)

theorem awaiting (before : Owned context (.sending (skb :: rest)) history ledger debts entry)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet entry)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (front : runPrefix (socketFront context.pid packet peer ipv4) entry
      (history.filterMap CausalJournal.completion?) =
        (.ok (result,frontWorld),history.filterMap CausalJournal.completion? ++ events)) :
    Nonempty (Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) := by
  have body := body_cases context.pid packet peer ipv4 entry (history.filterMap CausalJournal.completion?)
  rw [front] at body
  obtain ⟨chosen,member,head,_,after,done⟩ := Converse.socket_cut before complete packetAt peerValid body
  exact ⟨⟨before,complete,packetAt,peerValid,front,chosen,member,head,after,done⟩⟩

variable {context : Context} {skb : SkbId} {rest : List SkbId}
  {packet : RunWitness DataPacket} {peer : RunWitness Peer} {ipv4 : Bool}
  {history : List CausalJournal.Event} {ledger : Ledger} {debts : List CleanupDebt}
  {entry frontWorld : World} {result : Except Int SentDatagram} {events : List Completion.Event}

def Awaiting.prior (_point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :=
  history ++ events.map FirstTerminal.encode

def Awaiting.outcome (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    Staged.Obligations.Terminal := .socket point.prior.length (resultCode result == 0)

theorem Awaiting.prefix (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    runPrefix (FirstTerminal.focused (socketFront context.pid packet peer ipv4)) entry history =
      (.ok (result,frontWorld),point.prior) :=
  focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ entry history _ events point.front

theorem Awaiting.body (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    runPrefix (socketBody context.pid packet peer ipv4) entry (history.filterMap CausalJournal.completion?) =
      (.ok (resultCode result,resultWorld frontWorld result),history.filterMap CausalJournal.completion? ++ events) := by
  rw [body_cases,point.front]

theorem Awaiting.native (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    (receipt context.pid skb packet peer ipv4 entry result frontWorld).Valid :=
  (FirstTerminal.inner_cut context.pid skb packet peer ipv4 entry (resultWorld frontWorld result)
    history events (resultCode result) point.packetAt.1 point.peerValid point.body).1

theorem Awaiting.front_owned (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    Owned context (.sending (skb :: rest)) point.prior ledger debts frontWorld := by
  have view := socket_entry_view _ point.native
  have frontView := (result_view frontWorld result).symm.trans view
  exact (point.before.append (events.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births value)).same_view frontView

theorem Awaiting.front_complete (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    Complete point.prior ledger :=
  point.complete.append_quiet (Converse.completion_events_quiet
    (Converse.no_socket_suffix (Converse.socket_body_no_socket context.pid packet peer ipv4) point.body))

/-- The result suffix emits precisely the existing inner receipt and does not
rerun the socket, append another datagram, or perform another settlement. -/
theorem Awaiting.receipt_total (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    runPrefix (do
      emitPrefix (CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld)))
      pure (resultCode result)) (resultWorld frontWorld result) point.prior =
      (.ok (resultCode result,resultWorld frontWorld result),point.prior ++
        [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld))]) := rfl

theorem Awaiting.source (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4)) entry history =
      (.ok (resultCode result,resultWorld frontWorld result),point.prior ++
        [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld))]) :=
  (FirstTerminal.inner_cut context.pid skb packet peer ipv4 entry (resultWorld frontWorld result)
    history events (resultCode result) point.packetAt.1 point.peerValid point.body).2

theorem Awaiting.pending (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    point.chosen.pending ledger :=
  (point.before.cursor.assigned point.chosen point.member).1 (by simp [point.head])

theorem Awaiting.terminal (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events) :
    (point.chosen.ticket,Status.terminal point.outcome) ∈ settle [point.chosen.ticket] point.outcome ledger := by
  apply List.mem_map.mpr
  exact ⟨(point.chosen.ticket,Status.pending (.allocated point.chosen.position point.chosen.ordinal)),
    point.pending,by simp⟩

theorem Awaiting.first_preserved (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events)
    (step : Staged.Obligations.Step (settle [point.chosen.ticket] point.outcome ledger) later)
    (member : (point.chosen.ticket,status) ∈ later) : status = .terminal point.outcome :=
  step.terminal_unchanged point.after.entry.core.valid point.terminal member

/-- Every subsequent callback runs from the actual result world and recorded
history, even if that callback stops. -/
theorem Awaiting.continuation (point : Awaiting context skb rest packet peer ipv4 history ledger debts entry result frontWorld events)
    (next : Int → PrefixM CausalJournal.Event α) :
    runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4) >>= next) entry history =
      runPrefix (next (resultCode result)) (resultWorld frontWorld result)
        (point.prior ++ [CausalJournal.Event.old (.socket (receipt context.pid skb packet peer ipv4 entry result frontWorld))]) := by
  rw [runPrefix_bind,point.source]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
