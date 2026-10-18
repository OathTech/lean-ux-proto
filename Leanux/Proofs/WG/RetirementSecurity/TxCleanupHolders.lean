import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders

/-! The rejected createData path pays its saved key and peer references
before freeing the packet list. Its separation condition survives peer
release because a native put can only retain or remove an existing queue. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem TxDetached.peer_put (detached : TxDetached items w) (pid : PeerId)
    (a b : Ambient) (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    TxDetached items v := by
  cases device : w.dev with
  | none =>
    simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
      invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases stored : d.peers[pid]? with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
      by_cases positive : 0 < p.refcount
      · have nonzero : p.refcount ≠ 0 := by omega
        by_cases final : p.refcount = 1
        all_goals
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
            lift,liftIndex_run,retirePeerUnits,modifyAmbient,
            CounterWindow.branch_run,CounterWindow.branchCmp_run,
            device,stored,positive,nonzero,final,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
        all_goals repeat' first | split at run | contradiction
        all_goals rcases run with ⟨rfl,rfl⟩
        all_goals intro other q found batch queued head first
        all_goals by_cases same : pid = other
        all_goals simp [peerAt,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,same] at found
        all_goals first
          | (subst other; subst q;
             exact detached pid p (by simp [peerAt,device,stored]) batch queued head first)
          | exact detached other q (by simpa [peerAt,device] using found) batch queued head first
      · have zero : p.refcount = 0 := by omega
        simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
          refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
          CounterWindow.branchCmp_run,device,stored,zero,
          StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
          CounterWindow.except_ok_bind,CounterWindow.except_pure,
          unsupported,AmbientM.unsupported] at run
        cases run

theorem HolderAccount.cleanup_tx (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩)
    (head : items.head? = some first) (detached : TxDetached items w)
    (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((Queues.TxDisposition.cleanupSource pid items first).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  simp only [Queues.TxDisposition.cleanupSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,aa,readRun,_,t,ab,keyRun,_,s,ac,peerRun,freeRun⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := Packets.getTxSkb_current first w u packet a aa readRun
  subst u
  subst aa
  have named : nameLoan w (.transmit pid items) packet.keypair = some ⟨.transmit pid items,allocation⟩ := by
    simpa [transmitLoan,head,device,stored] using batch
  have slot : allocation.slot = packet.keypair := (nameLoan_resident named).2.1
  rw [←slot] at keyRun
  have ht := account.put false a ab keyRun
  have unchanged := put_peers (some allocation.slot) false w t a ab keyRun
  have readyT := ready.peers unchanged
  have detachedT := detached.peers unchanged
  have hs := ht.peer_put readyT ab ac peerRun
  have detachedS := detachedT.peer_put pid ab ac peerRun
  exact (hoare_iff_run_ambient _ _ _).mp (free_list_holders items temporary)
    s ac () v b ⟨hs,detachedS⟩ freeRun

end Leanux.Proofs.WG.RetirementSecurity
