import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxFrames

/-! RX allocation consumes the actual acquired loan into one unpublished
carrier at the native allocation frontier. The old queued carrier ledger
remains stable; the new cell is not prematurely called queued. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem allocate_rx_peers (pkt : RxPacket) : SameView peerView (newRxSkb pkt) := by
  intro initial
  unfold newRxSkb
  apply hoare_liftSkb
  intro w d store hi device
  simpa only [peerView,device,Option.map_some,Option.bind_some] using hi

theorem allocate_rx_holders (pkt : RxPacket) (initial : WGWorld) :
    Preserves (Frame initial) (newRxSkb pkt) := by
  unfold newRxSkb
  apply hoare_liftSkb
  intro w d store hi device
  exact hi.trans (by constructor <;> first
    | (simp [passiveView,sendView,device])
    | (intro q xs h; simpa [handoffTxView,device] using h))

theorem allocate_rx_stable {id : SkbId} (stable : StableRx carriers w)
    (inventory : Inventory carriers w) (fresh : Packets.Inv w) (pkt : RxPacket)
    (a b : Ambient) (run : ((newRxSkb pkt).run w).run a = .ok ((id,v),b)) :
    StableRx carriers v := by
  cases device : w.dev with
  | none => simp [newRxSkb,liftSkb_run,device] at run
  | some d =>
    rw [Packets.newRxSkb_run w a d pkt device] at run
    cases run
    simpa only [Packets.update,device,Option.map_some] using
      stable.allocate inventory device (Packets.allocation_slots_empty w d device fresh).2 pkt

theorem Account.rx_allocate {id : SkbId} {pkt : RxPacket}
    (account : Account holders carriers (owner :: loans) w) (fresh : Packets.Inv w)
    (peer : owner.slot = pkt.peer) (key : KeyCompatible pkt.peer pkt.keypair w)
    (a b : Ambient) (run : ((newRxSkb pkt).run w).run a = .ok ((id,v),b)) :
    ∃ c, c.packet = ⟨owner.epoch,id⟩ ∧ c.owner = owner ∧ c.phase = .unpublished ∧
      Phased holders (c :: carriers) loans v ∧ StableRx carriers v := by
  have input := WorkReservations.carrier_loans_perm account.funded.carriers List.perm_middle
  obtain ⟨c,packet,ownerEq,phase,funded⟩ := allocate_state input fresh peer key a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (allocate_rx_holders pkt w)
    w a id v b (Frame.refl w) run
  have before : Upper holders carriers (c.owner :: loans) w := by simpa only [ownerEq] using account.upper
  have upper := (before.loan_to_carrier (by simp only [phase,Phase.charged])).peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (allocate_rx_peers pkt) w a id v b run)
  exact ⟨c,packet,ownerEq,phase,⟨⟨account.funded.aligned.frame frame,funded⟩,upper⟩,
    allocate_rx_stable account.stable account.funded.carriers.inventory fresh pkt a b run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
