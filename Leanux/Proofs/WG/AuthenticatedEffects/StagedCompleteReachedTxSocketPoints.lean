import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSocketSource

/-! Socket points contain only the original read, selected family and
successful front. Native result and receipt emission are fixed total suffixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal SocketInterior

structure Entry (pid : PeerId) (packet : RunWitness DataPacket) (w : World) (h : List CausalJournal.Event) where
  peer : RunWitness Peer
  readWorld : World
  readEvents : List Completion.Event
  read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
    (h.filterMap CausalJournal.completion?)=(.ok (peer,readWorld),h.filterMap CausalJournal.completion?++readEvents)
  ipv4 : Bool
  family : SelectedFamily ipv4 peer
  result : Except Int SentDatagram
  frontWorld : World
  events : List Completion.Event
  front : runPrefix (socketFront pid packet peer ipv4) (familyWorld ipv4 readWorld)
    ((h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?)=
    (.ok (result,frontWorld),(h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?++events)

def Entry.history (entry : Entry pid packet w h) : List CausalJournal.Event :=
  (h++entry.readEvents.map FirstTerminal.encode)++entry.events.map FirstTerminal.encode

def Entry.socket (entry : Entry pid packet w h) (skb : SkbId) : Completion.SocketReceipt :=
  receipt pid skb packet entry.peer entry.ipv4 (familyWorld entry.ipv4 entry.readWorld) entry.result entry.frontWorld

def Entry.remaining (entry : Entry pid packet w h) (skb : SkbId) (phase : Phase) : PrefixM CausalJournal.Event Bool :=
  outer pid skb packet w (innerRemaining phase pid skb packet entry.peer entry.ipv4
    (familyWorld entry.ipv4 entry.readWorld) entry.result entry.frontWorld)

theorem Entry.continuation (entry : Entry pid packet w h) (skb : SkbId) (phase : Phase) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w h=
      runPrefix (entry.remaining skb phase) (cutWorld phase entry.frontWorld entry.result)
        (cutHistory phase entry.history (entry.socket skb)) :=
  TxSocket.continuation entry.read entry.family entry.front phase

inductive Point (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (w : World) (h : List CausalJournal.Event) : World → List CausalJournal.Event → Prop where
  | source (entry : Entry pid packet w h) (phase : Phase) :
      Point pid skb packet w h (cutWorld phase entry.frontWorld entry.result)
        (cutHistory phase entry.history (entry.socket skb))

theorem Point.remaining (point : Point pid skb packet w h u middle) :
    ∃remaining,runPrefix (CausalJournal.completionOps.send pid skb packet) w h=runPrefix remaining u middle := by
  cases point with
  | source entry phase=>exact ⟨_,entry.continuation skb phase⟩

noncomputable def remainder (point : Point pid skb packet w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid skb packet w h u middle) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
