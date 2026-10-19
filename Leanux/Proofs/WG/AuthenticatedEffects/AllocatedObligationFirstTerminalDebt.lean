import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSupport
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalUnsupported

/-! Actual first-terminal source cuts retain the selected allocation as debt,
including errno and unsupported-family refusal. Pending coverage, converse
coverage and mixed ticket uniqueness are transported together. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- The actual inner socket result moves precisely this pending allocation
to cleanup debt, including on errno. The physical cell remains backed and no
other fixed ticket can claim it. All source-entry support remains explicit. -/
theorem inner_debt (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history : List CausalJournal.Event) (middle : List Completion.Event) (ret : Int)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle))
    (support : Support births history ledger debts w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Completion.SocketReceipt := ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let before := history ++ middle.map encode
    let outcome := Staged.Obligations.Terminal.socket before.length (ret == 0)
    let after := settle [ticket] outcome ledger
    let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
    let journal := before ++ [CausalJournal.Event.old (.socket receipt)]
    runPrefix (focused (Completion.socket pid skb packet peer ipv4)) w history =
      (.ok (ret,v),journal) ∧ Staged.Obligations.Step ledger after ∧
      Support births journal after (debt :: debts) v.wg ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      Origin journal position ordinal generation skb value ∧
      Packets.epoch v.wg = some generation ∧ PacketMaterial.view v.wg skb = some value := by
  dsimp only
  obtain ⟨native,observed⟩ := inner_cut pid skb packet peer ipv4 w v history middle ret
    packetValid peerValid performed
  have views := socket_views _ native
  have atSocket := (support.views views.1 views.2.2).append (middle.map encode)
  obtain ⟨step,settled,terminal⟩ := atSocket.settle pending
    (.socket (history ++ middle.map encode).length (ret == 0))
  have selected := (support.resident ticket position ordinal pending).at_origin origin
  exact ⟨observed,step,settled.append _,terminal,(origin.append _).append _,
    views.1.trans selected.1,(congrFun views.2.2 skb).trans selected.2⟩

/-- The actual unsupported-family arm has no socket event in its suffix and
keeps the same resident allocation as terminal cleanup debt. It cannot stand
in for an inner errno whose earlier result has already settled the ticket. -/
theorem unsupported_debt (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history : List CausalJournal.Event)
    (middle : List Completion.Event)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6)
    (support : Support births history ledger debts w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨pid,skb,packet,⟨false,w,v⟩⟩
    let before := history ++ middle.map encode
    let outcome := Staged.Obligations.Terminal.sendRefused before.length
    let after := settle [ticket] outcome ledger
    let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
    let journal := before ++ [CausalJournal.Event.sendResult receipt]
    middle.filterMap Completion.socket? = [] ∧
      runPrefix (SendResult.observed CausalJournal.Event.sendResult
        (focused (Completion.send pid skb packet)) pid skb packet) w history =
        (.ok (false,v),journal) ∧ Staged.Obligations.Step ledger after ∧
      Support births journal after (debt :: debts) v.wg ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      Origin journal position ordinal generation skb value ∧
      Packets.epoch v.wg = some generation ∧ PacketMaterial.view v.wg skb = some value := by
  dsimp only
  obtain ⟨_,world,noSocket,observed⟩ := unsupported_cut pid skb packet peer w u history middle
    packetValid read not4 not6
  have atEnd : Support births history ledger debts (CompletionFirstTerminal.refusedWorld u).wg := by
    rw [world]
    exact support
  obtain ⟨step,settled,terminal⟩ := (atEnd.append (middle.map encode)).settle pending
    (.sendRefused (history ++ middle.map encode).length)
  have selected := (support.resident ticket position ordinal pending).at_origin origin
  exact ⟨noSocket,observed,step,settled.append _,terminal,(origin.append _).append _,
    by rw [world]; exact selected.1,by rw [world]; exact selected.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
