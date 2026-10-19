import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxPublicationFrames

/-! The actual enqueue changes the unpublished carrier's phase only when
the peer queue accepts it. No new reference is inferred from queue insertion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Phased.rx_enqueue {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (phase : c.phase = .unpublished)
    (stored : packetAt w c.packet = some pkt) (owner : pkt.peer = c.owner.slot)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeerRx c.packet.slot).run w).run a = .ok ((ret,v),b)) :
    (ret = 0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      Phased holders ((if ret = -ENOSPC then c else enqueued c) :: carriers) loans v := by
  obtain ⟨choices,funded⟩ := enqueue_state account.funded.carriers phase stored owner a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.enqueue_frame c.packet.slot w)
    w a ret v b (Frame.refl w) run
  refine ⟨choices,⟨⟨account.funded.aligned.frame frame,funded⟩,?_⟩⟩
  have charged : 0 < demand (c :: carriers) (holders.owners ++ loans) c.owner := by
    simp [demand,charges,phase,Phase.charged]
    omega
  obtain ⟨p,resident,_⟩ := protected_resident account.funded.carriers.funded charged
  obtain ⟨d,device,epoch,peer,_⟩ := resident_fields resident
  have ep : d.ifindex = c.packet.epoch :=
    epoch.trans (account.funded.carriers.inventory.present c (by simp)).1.symm
  have cell : d.rxSkbs[c.packet.slot]? = some pkt := by simpa [packetAt,device,ep] using stored
  have peerAt : d.peers[pkt.peer]? = some p := by simpa [owner] using peer
  obtain ⟨_,cpu,state⟩ := enqueue_effect device cell peerAt a b run
  have dev := congrArg WGStoreView.dev state
  change v.dev = some (enqueueDevice d c.packet.slot pkt p ret cpu) at dev
  intro other
  have same : balance v other = balance w other := by
    calc balance v other = balance {w with dev := some (enqueueDevice d c.packet.slot pkt p ret cpu)} other := by
           simp only [balance,RxCredits.resident,dev]
         _ = _ := enqueue_balance device peerAt other
  rw [same]
  have old := account.upper other
  by_cases full : ret = -ENOSPC
  · simpa only [ite_eq_left full] using old
  · by_cases sameOwner : c.owner = other <;>
      simpa [ite_eq_right full,demand,charges,enqueued,List.filter_cons,phase,Phase.charged,sameOwner] using old

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
