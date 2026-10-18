import Leanux.Proofs.WG.RetirementSecurity.PeerReleaseHolders

/-! The native zero-material worker discharges final-peer slot readiness
itself: handshake clearing retains holders, keypairsClear pays the actual
three slots, and the concluding peer put can erase only an empty holder
group. Its incoming concrete holder account remains a caller obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem updatePeer_holders (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, slotFields (f p) = slotFields p ∧
      (f p).txQueue = p.txQueue ∧ (f p).rxQueue = p.rxQueue)
    (temporary : Credits.Ledger) : Preserves (HolderAccount temporary) (updatePeer pid f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  cases result
  rw [updatePeer,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,setRun⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have final : v = replacePeer w d pid (f p) := by
    have pair : replacePeer w d pid (f p) = v ∧ a = b := by
      simpa [setPeer,modifyDev,replacePeer,device] using setRun
    exact pair.1.symm
  rw [final]
  exact account.peer_fields device stored (fields p)

theorem index_holderStore (action : IndexM α) : SameView holderStore (liftIndex action) := by
  intro initial
  apply hoare_liftIndex action
  intro w d table same device
  simpa [holderStore,Origins.view,peersAt,packetKeyWords,device] using same

theorem handshakeZero_holders (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (handshakeZero pid) := by
  change Preserves (HolderAccount temporary) (updatePeer pid zeroedPeer)
  exact updatePeer_holders pid zeroedPeer (fun _ => ⟨rfl,rfl,rfl⟩) temporary

theorem handshakeClear_holders (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (handshakeClear pid) := by
  unfold handshakeClear
  apply preserves_bind (indexOwner_peerDeref_preserves _ (HolderAccount temporary))
  intro _
  apply preserves_bind (holderStore_preserves _ (index_holderStore _) temporary)
  intro _
  exact handshakeZero_holders pid temporary

theorem HolderAccount.zero_worker (account : HolderAccount temporary w)
    (pid : PeerId) (a b : Ambient)
    (run : ((queuedExpiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧ SlotsCleared pid v ∧ Retains w v := by
  have retired := zero_worker_retirement pid w v a b run
  simp only [queuedExpiredZeroKeyMaterial,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,handshakeRun,_,t,e,clearRun,putRun⟩ := run
  have hu := (hoare_iff_run_ambient _ _ _).mp (handshakeClear_holders pid temporary)
    w a () u c account handshakeRun
  have ht := (hoare_iff_run_ambient _ _ _).mp (clear_holders pid temporary)
    u c () t e hu clearRun
  have cleared := (hoare_iff_run_ambient _ _ _).mp (clear_slots pid)
    u c () t e True.intro clearRun
  have ready : PeerReleaseReady pid t := fun p found _ => cleared p found
  exact ⟨ht.peer_put ready e b putRun,retired⟩

theorem flushed_holders (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (runFlushedClearWork pid) := by
  have callback : Preserves (HolderAccount temporary) (queuedExpiredZeroKeyMaterial pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b account run
    cases result
    exact (account.zero_worker pid a b run).1
  unfold runFlushedClearWork
  apply preserves_bind (holderStore_preserves _
    (modifyDev_holderStore (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) temporary)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker))
    (HolderAccount temporary))
  intro _
  apply preserves_bind callback
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker))
    (HolderAccount temporary))
  intro _
  exact preserves_pure ()

theorem HolderAccount.dispatched_zero (account : HolderAccount temporary w.wg)
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    HolderAccount temporary v.wg ∧ ∃ d pid,
      w.wg.dev = some d ∧ pid ∈ d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg := by
  obtain ⟨d,_,_,_,pid,beforeWorker,device,_,_,_,member,worker⟩ :=
    Queues.RxCredits.ClearWork.runOneClearWorker_selected w v run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (flushed_holders pid temporary)
      w.wg beforeWorker () v.wg v.ambient account worker,
    d,pid,device,member,flushed_retirement pid w.wg v.wg beforeWorker v.ambient worker⟩

end Leanux.Proofs.WG.RetirementSecurity
