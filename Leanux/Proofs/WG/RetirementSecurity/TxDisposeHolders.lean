import Leanux.Proofs.WG.RetirementSecurity.PeerReleaseHolders

/-! The original TX worker disposal frees the saved packet list, pays its
one key reference, then pays its peer reference. The actual durable account
is rebuilt after all three operations; no extra key credit is inferred from
the independent peer reference budget. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem packet_peer_frame (action : SkbM α) : SameView peersAt (liftSkb action) := by
  intro initial
  apply hoare_liftSkb action
  intro w d store same device
  simpa [peersAt,device] using same

theorem free_list_peer_frame (items : List SkbId) :
    SameView peersAt (Queues.TxDisposition.freeList items) := by
  induction items with
  | nil => exact SameView.pure _ _
  | cons id rest ih =>
    rw [Queues.TxDisposition.freeList_cons]
    exact (packet_peer_frame (SkbStore.freeTx id)).bind (fun _ => ih)

theorem PeerReleaseReady.peers (ready : PeerReleaseReady pid w)
    (same : peersAt v = peersAt w) : PeerReleaseReady pid v := by
  intro p found final
  apply ready p _ final
  simpa only [peerAt,show v.dev.bind (fun d => d.peers[pid]?) =
      w.dev.bind (fun d => d.peers[pid]?) from by
    simpa [peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun peers => peers.bind fun entries => entries[pid]?) same] using found

theorem TxDetached.peers (detached : TxDetached items w)
    (same : peersAt v = peersAt w) : TxDetached items v := by
  intro pid p found batch member head first
  apply detached pid p _ batch member head first
  simpa only [peerAt,show v.dev.bind (fun d => d.peers[pid]?) =
      w.dev.bind (fun d => d.peers[pid]?) from by
    simpa [peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun peers => peers.bind fun entries => entries[pid]?) same] using found

theorem HolderAccount.dispose_tx (account : HolderAccount (allocation :: temporary) w)
    (detached : TxDetached items w) (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items allocation.slot).run w).run a =
      .ok ((result,v),b)) : result = true ∧ HolderAccount temporary v := by
  have factor : Queues.TxDisposition.disposeSource pid items allocation.slot = (do
      Queues.TxDisposition.freeList items
      keypairPut (some allocation.slot) false
      peerPut (some pid)
      pure true) := by simp [Queues.TxDisposition.disposeSource,Queues.TxDisposition.freeList]
  rw [factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,aa,freeRun,_,t,ab,keyRun,_,s,ac,peerRun,tail⟩ := run
  have hu := (hoare_iff_run_ambient _ _ _).mp
    (free_list_holders items (allocation :: temporary)) w a () u aa ⟨account,detached⟩ freeRun
  have readyU := ready.peers ((ProjectedAction.iff_run_ambient _ _ _).mp
    (free_list_peer_frame items) w a () u aa freeRun)
  have ht := hu.put false aa ab keyRun
  have readyT := readyU.peers (put_peers (some allocation.slot) false u t aa ab keyRun)
  have hs := ht.peer_put readyT ab ac peerRun
  cases tail
  exact ⟨rfl,hs⟩

end Leanux.Proofs.WG.RetirementSecurity
