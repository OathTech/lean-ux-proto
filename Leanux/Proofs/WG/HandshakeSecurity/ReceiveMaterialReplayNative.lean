import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialReplayEntry
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayAuthorizedPoll

/-! Actual RX selection preserves the allocation certificate through native poll guards. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {skb : SkbId} {pkt : RxPacket}

abbrev Preserves (g : PrefixM E α) := PrefixPreserves (Inv origin replay) (Safe origin replay) g

theorem native (action : WG.M α)
    (frame : ∀ h, Leanux.Proofs.Framing.Preserves (ReceiveMaterial.Inv h) action) :
    Preserves (origin := origin) (replay := replay) (liftPrefix (liftWG action)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w x v hi run
  exact ⟨(hoare_iff_run _ _ _).mp
    (PublicationPoll.native_product _ _ (frame (h.filterMap origin))) w x v hi.1 run,hi.2⟩

theorem picked_native (action : WG.M α) (packets : SameView RxDisposition.nativeRxStore action)
    (frame : ∀ h, Leanux.Proofs.Framing.Preserves (ReceiveMaterial.Inv h) action) :
    PrefixPreserves (Picked origin replay skb pkt) (Safe origin replay) (liftPrefix (liftWG action)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
  intro h w x v hi run
  have kept := (hoare_iff_run _ _ _).mp
    (PublicationPoll.native_product _ _ (frame (h.filterMap origin))) w x v hi.1.1 run
  have product := sameView_liftWG RxDisposition.rxStore RxDisposition.nativeRxStore action packets
    (fun _ _ _ equal => equal)
  have same := (ProjectedAction.iff_run _ _ _).mp product w x v run
  exact ⟨⟨kept,hi.1.2⟩,(congrFun (congrArg Prod.snd same) skb).trans hi.2⟩

theorem read_selected (skb : SkbId) :
    PrefixEnsures (Inv origin replay) (Safe origin replay) (liftPrefix (liftWG (getRxSkb skb)))
      (fun pkt => Picked origin replay skb pkt) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w pkt v hi run
  rw [liftWG_run] at run
  cases nativeRun : ((getRxSkb skb).run w.wg).run w.ambient with
  | error err => simp [nativeRun,Except.map] at run
  | ok out =>
    rcases out with ⟨⟨packet,u⟩,a⟩
    simp only [nativeRun,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    obtain ⟨same,ambient,d,hd,hp⟩ := Packets.getRxSkb_current skb w.wg u packet w.ambient a nativeRun
    subst u
    subst a
    exact ⟨hi,by simp [RxDisposition.nativeRxStore,hd,hp]⟩

theorem state_bind (f : Bool → PrefixM E α)
    (next : ∀ bad, bad = (pkt.state != .crypted) →
      PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (f bad) Q) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (liftPrefix (liftWG (branch .rxPollNotCrypted (pkt.state != .crypted))) >>= f) Q := by
  apply PrefixEnsures.bind (Q := fun bad h w => Picked origin replay skb pkt h w ∧ bad = (pkt.state != .crypted))
  · apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
    intro h w bad v hi run
    cases run
    exact ⟨hi,rfl⟩
  · intro bad w h hi
    exact next bad hi.2 w h hi.1

theorem crypted_of_test (s : PacketState) (negative : (s != .crypted) = false) : s = .crypted := by
  cases s <;> first | rfl | cases negative

macro "receive_material_native_frame" : tactic => `(tactic| (
  try simp (config := {zeta := false}) only [WG.andM,branch,branchCmp,invariant,unsupported]
  repeat' first
    | (rx_retention_head getPeer; exact ReceiveMaterial.read_peer _)
    | (rx_retention_head setPeer; exact ReceiveMaterial.set_peer _ _)
    | (rx_retention_head getRxSkb; exact ReceiveMaterial.read_rx _)
    | (rx_retention_head freeRxSkb; exact ReceiveMaterial.free_rx _)
    | (rx_retention_head peerPut; exact ReceiveMaterial.peer_put _)
    | (rx_retention_head keypairPut; exact ReceiveMaterial.key_put _ _)
    | (rx_retention_head PrevQueue.peek; exact ReceiveMaterial.store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head endpointFromSkb; exact ReceiveMaterial.store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head getDev; exact ReceiveMaterial.store getDev_sameWGStore)
    | (first | rx_retention_head MonadLift.monadLift | rx_retention_head MonadLiftT.monadLift
       exact hoare_liftAmbient _ _)
    | (rx_retention_head Pure.pure; exact preserves_pure _)
    | (rx_retention_head Bind.bind; apply preserves_bind)
    | (rx_retention_head ite; split)
    | keypairs_intro_forall
    | rx_retention_step))

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
