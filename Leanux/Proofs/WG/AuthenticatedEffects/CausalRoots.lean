import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedParents
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCompletionParents

/-! Finite causal explanations for protected native effects. Inherited timer,
work and completion contexts follow strictly earlier native occurrences; a label
alone is never a terminal authenticated root. These constructors deliberately
expose the exact receipt and occurrence evidence used by the final claim. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def AuthenticatedReceive (index : Nat) (skb : SkbId) (packet : RxPacket) (history : List Event) : Prop :=
  ∃ start receipt rest,
    history = start ++ [Coverage.candidate index skb packet,Coverage.replay receipt] ++ rest ∧
    index = start.length ∧ receipt.skb = skb ∧ receipt.packet = packet ∧ receipt.run.value = true ∧
    TransportReplay.Certified
      ((start ++ [Coverage.candidate index skb packet]).filterMap StackOrigins.origin?) receipt

/-- A finite explanation ends at an actual fixture scope or the native
handshake/transport receipt for its own occurrence. Every inherited step records
its native parent and the precise earlier prefix whose cause is explained next. -/
inductive Rooted : List Event → Prop where
  | fixture (history : List Event) (index : Nat) (trigger : FixtureEffects.Trigger)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.fixture trigger⟩))
      (before after : List Event)
      (entered : history = before ++ .scope (.entered ⟨index,.fixture trigger⟩) :: after) : Rooted history
  | handshake (history : List Event) (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.handshake kind pid⟩))
      (before after : List Event)
      (paired : history = before ++
        [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ after)
      (admission : HandshakeFresh.Available (before.filterMap handshake?) pid) : Rooted history
  | candidate (history : List Event) (index : Nat) (skb : SkbId) (packet : RxPacket)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.candidate skb packet⟩))
      (authenticated : AuthenticatedReceive index skb packet history) : Rooted history
  | stackInput (history : List Event) (index : Nat) (entry : GroOccurrence.Entry)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.stackInput entry⟩))
      (before after : List Event)
      (entered : history = before ++ .scope (.entered ⟨index,.stackInput entry⟩) :: after)
      (authenticated : AuthenticatedReceive entry.scope entry.skb entry.packet before) : Rooted history
  | timer (history : List Event) (index : Nat) (bound : UInt64) (pid : PeerId)
      (timer : PeerTimer) (entry : WheelEntry)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.timer bound pid timer entry⟩))
      (before after : List Event) (arm : TimerEffects.Arm Context) (stamp : Nat) (expires : Option UInt64)
      (earlier : history = before ++ .armed arm :: after)
      (native : arm.Valid) (changed : TimerOccurrences.Changed arm)
      (peer : arm.peer = pid) (kind : arm.timer = timer)
      (pending : TimerSlots.Pending arm.run.after pid timer stamp expires entry)
      (cause : arm.cause = CausalScope.current scope? before)
      (parent : Rooted before) : Rooted history
  | work (history : List Event) (index : Nat) (pid : PeerId) (entry : CausalSources.SendEntry)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.sendWork pid entry⟩))
      (before after : List Event) (queued : TimerEffects.Queued Context)
      (earlier : history = before ++ .queued queued :: after)
      (native : queued.Valid) (peer : queued.peer = pid)
      (cause : queued.cause = CausalScope.current scope? before)
      (parent : Rooted before) : Rooted history
  | completion (history : List Event) (index : Nat) (pid : PeerId) (items : List SkbId)
      (current : CausalScope.current scope? history = .ok (some ⟨index,.completion pid items⟩))
      (scopeBefore rest : List Event)
      (paired : history = scopeBefore ++
        [.scope (.entered ⟨index,.completion pid items⟩),.old (.disposition (.completion pid items))] ++ rest)
      (before after : List Event) (packets : List DataPacket) (run : WGRunWitness (List SkbId))
      (id : SkbId) (tail : List SkbId) (generation : Nat) (packet : DataPacket)
      (earlier : scopeBefore = before ++ .old (.allocated packets run) :: after)
      (shape : items = id :: tail) (native : run.Valid (packets.mapM newTxSkb))
      (epoch : PacketOrigins.epoch run.after = some generation)
      (ordinal : Nat) (original : DataPacket)
      (atPacket : packets[ordinal]? = some original) (atId : run.value[ordinal]? = some id)
      (material : PacketMaterial.material original = packet)
      (parent : Rooted before) : Rooted history

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
