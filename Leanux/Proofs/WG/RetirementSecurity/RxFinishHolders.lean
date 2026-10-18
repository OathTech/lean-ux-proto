import Leanux.Proofs.WG.RetirementSecurity.RxPublishHolders
import Leanux.Proofs.WG.RetirementSecurity.RxCleanupHolders

/-! The original RX post-allocation caller transfers its saved key credit
on peer-queue admission and pays it on refusal. Allocation identity,
detachment and peer-release readiness are explicit caller facts here;
there is no assumed post-enqueue ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.discard_rx {id : SkbId}
    (account : HolderAccount (allocation :: temporary) w)
    (pkt : RxPacket) (key : pkt.keypair = allocation.slot)
    (detached : RxDetached id w) (ready : PeerReleaseReady pkt.peer w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.discard id pkt).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  simp only [Queues.RxCredits.discard,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,keyRun,_,t,e,peerRun,freeRun⟩ := run
  rw [key] at keyRun
  have hu := account.put false a c keyRun
  have samePeers := put_peers (some allocation.slot) false w u a c keyRun
  have ht := hu.peer_put (ready.peers samePeers) c e peerRun
  exact ht.free_rx ((detached.peers samePeers).peer_put pkt.peer c e peerRun) e b freeRun

theorem HolderAccount.finish_rx
    (account : HolderAccount (allocation :: temporary) w)
    (ctx : RxOrigin.Admission)
    (device : w.dev = some d) (packet : d.rxSkbs[ctx.slot]? = some ctx.packet)
    (peer : d.peers[ctx.packet.peer]? = some p)
    (loan : receiveLoan w ctx.packet.peer ctx.slot =
      some ⟨.receive ctx.packet.peer ctx.slot,allocation⟩)
    (key : ctx.packet.keypair = allocation.slot)
    (detached : RxDetached ctx.slot w) (ready : PeerReleaseReady ctx.packet.peer w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.finishSource ctx).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  have whole := run
  rw [Queues.RxCredits.finish_factor] at run
  obtain ⟨ret,u,c,enqueueRun,tail⟩ := (by
    simpa only [MaterialOrigin.bind_ok_ambient] using run)
  rcases account.enqueue_rx_native device packet peer loan a c enqueueRun with
    ⟨refused,hu,fields⟩ | ⟨accepted,hu⟩
  · subst ret
    have cleanup := (Queues.RxCredits.finish_enospc ctx a c enqueueRun).symm.trans whole
    have peers : peersAt u = peersAt w := congrArg (fun store => store.2.1) fields
    exact hu.discard_rx ctx.packet key (detached.peers peers) (ready.peers peers)
      (Queues.RxCredits.enospcDecisions c) b cleanup
  · rcases accepted with rfl | rfl
    · have same : v = u := by
        simp [Queues.RxCredits.finishAfter,WG.orM,branch,AmbientM.branch,Leanux.EPIPE,
          StateT.run_bind,StateT.run_monadLift] at tail
        exact tail.1.symm
      exact same.symm ▸ hu
    · simp only [Queues.RxCredits.finishAfter,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨decision,z,e,branchRun,tail⟩ := tail
      change Except.ok ((true,u),CounterWindow.record c .dataEpipe true) =
        .ok ((decision,z),e) at branchRun
      cases branchRun
      simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,s,f,publishRun,tail⟩ := tail
      have hs := hu.publish_rx ctx.slot .dead _ f publishRun
      have same : v = s := by
        simp [WG.orM,branch,AmbientM.branch,WG.EPIPE,Leanux.EPIPE,
          StateT.run_bind,StateT.run_monadLift] at tail
        exact tail.1.symm
      exact same.symm ▸ hs

end Leanux.Proofs.WG.RetirementSecurity
