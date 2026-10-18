import Leanux.Proofs.WG.RetirementSecurity.RxStoreHolders
import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders

/-! Original RX poll cleanup pays its selected packet's key reference,
then its peer reference, then frees the detached packet. Existing concrete
queue-retention facts permit final peer deletion without losing another
holder. Full poll callback and initialized-driver coverage remain separate. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
variable {id : SkbId}

theorem RxDetached.retained (detached : RxDetached id w)
    (retained : ResidentsRetained (Queues.rxQueues w) (Queues.rxQueues v)) : RxDetached id v := by
  intro pid p found
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp found
  have before := retained pid ⟨d.ifindex,p.internalId,p.rxQueue⟩
    (by simp [Queues.rxQueues,Queues.rxMap,device,stored])
  cases oldDevice : w.dev with
  | none => simp [Queues.rxQueues,oldDevice] at before
  | some old =>
    have cell : (old.peers[pid]?).map (fun q => Queues.RxQueueCell.mk old.ifindex q.internalId q.rxQueue) =
        some ⟨d.ifindex,p.internalId,p.rxQueue⟩ := by
      simpa only [Queues.rxQueues,Queues.rxMap,oldDevice,Option.bind_some] using before
    obtain ⟨q,resident,fields⟩ := Option.map_eq_some_iff.mp cell
    have queue : q.rxQueue = p.rxQueue := congrArg Queues.RxQueueCell.queue fields
    exact queue ▸ detached pid q (by simp [peerAt,oldDevice,resident])

theorem RxDetached.peer_put (detached : RxDetached id w) (pid : PeerId)
    (a b : Ambient) (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    RxDetached id v := detached.retained
  ((ProjectedAction.iff_run_ambient _ _ _).mp (Queues.peerPut_rxQueues (some pid)) w a () v b run)

theorem RxDetached.peers (detached : RxDetached id w)
    (same : peersAt v = peersAt w) : RxDetached id v := by
  intro pid p found
  have cells : peerAt v pid = peerAt w pid := by
    simpa [peersAt,peerAt,Option.bind_map,Function.comp_def] using
      congrArg (fun peers => peers.bind fun entries => entries[pid]?) same
  exact detached pid p (cells.symm.trans found)

theorem HolderAccount.cleanup_rx {id : SkbId} (account : HolderAccount (allocation :: temporary) w)
    (pkt : RxPacket) (key : pkt.keypair = allocation.slot) (flag : Bool)
    (detached : RxDetached id w) (ready : PeerReleaseReady pkt.peer w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  simp only [Queues.RxCredits.cleanup,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,keyRun,_,t,e,peerRun,result,s,f,branchRun,freeRun⟩ := run
  rw [key] at keyRun
  have hu := account.put false a c keyRun
  have samePeers := put_peers (some allocation.slot) false w u a c keyRun
  have readyU := ready.peers samePeers
  have detachedU := detached.peers samePeers
  have ht := hu.peer_put readyU c e peerRun
  have detachedT := detachedU.peer_put pkt.peer c e peerRun
  have same : s = t := by cases branchRun; rfl
  subst s
  exact ht.free_rx detachedT f b freeRun

end Leanux.Proofs.WG.RetirementSecurity
