import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionSettlement

/-! The exact first-terminal socket or unsupported-family result advances
the selected send cursor. The receipt uses the same current packet store;
an independent historical packet read cannot discharge this cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

theorem socket_ownership (receipt : Completion.SocketReceipt) :
    SameView ownershipPointView receipt.action := by
  unfold Completion.SocketReceipt.action
  cases receipt.ipv4
  · exact (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_ownership) _ _ _ _ _
  · exact (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_ownership) _ _ _ _ _

/-- At the actual inner socket result, the same selected packet becomes
terminal cleanup debt even on errno. The observed cut precedes accounting. -/
theorem inner_advanced (before : State context (.sending (skb :: rest)) history w)
    (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let receipt : Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let journal := (history ++ middle.map FirstTerminal.encode) ++ [CausalJournal.Event.old (.socket receipt)]
    runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4)) w history =
      (.ok (ret,v),journal) ∧ State context (.sending rest) journal v := by
  dsimp only
  obtain ⟨native,observed⟩ := FirstTerminal.inner_cut context.pid skb packet peer ipv4 w v history middle ret
    packetAt.1 peerValid performed
  have kept := before.native _ (PacketOrigins.snapshot_wire (FirstTerminal.socket_wire _))
    (socket_ownership _) native.2.2
  have moved := kept.settle_head (.socket (history ++ middle.map FirstTerminal.encode).length (ret == 0))
  exact ⟨observed,(moved.append _).append _⟩

/-- Only the original unsupported-family arm supplies this uncounted
refusal. It has no inner socket event and advances the same resident cell. -/
theorem unsupported_advanced (before : State context (.sending (skb :: rest)) history w)
    (packetAt : PacketAt skb packet w)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : HandshakeSecurity.StagedConservation.SendResult.Receipt :=
      ⟨context.pid,skb,packet,⟨false,w,v⟩⟩
    let journal := (history ++ middle.map FirstTerminal.encode) ++ [CausalJournal.Event.sendResult receipt]
    middle.filterMap Completion.socket? = [] ∧
      runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
        (.ok (false,v),journal) ∧ State context (.sending rest) journal v := by
  dsimp only
  obtain ⟨_,world,noSocket,observed⟩ := FirstTerminal.unsupported_cut context.pid skb packet peer w u
    history middle packetAt.1 read not4 not6
  have kept := before.sameWG world
  have moved := kept.settle_head (.sendRefused (history ++ middle.map FirstTerminal.encode).length)
  exact ⟨noSocket,observed,(moved.append _).append _⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
