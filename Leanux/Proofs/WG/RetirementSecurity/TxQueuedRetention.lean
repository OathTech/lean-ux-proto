import Leanux.Proofs.WG.RetirementSecurity.TxCryptCompletion

/-! Native peer release cannot remove an owning TX queue on normal return:
its actual final-reference arm checks both packet queues before deletion.
This is a forward ownership fact, stronger than survivor-only field frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem TxQueuedBatch.peer_put (owned : TxQueuedBatch w items) (target : Option PeerId)
    (a b : Ambient)
    (run : ((peerPut target).run w).run a = .ok (((),v),b)) : TxQueuedBatch v items := by
  obtain ⟨owner,q,found,member⟩ := owned
  cases target with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨owner,q,found,member⟩
  | some pid =>
    cases device : w.dev with
    | none => simp [peerAt,device] at found
    | some d =>
      have old : d.peers[owner]? = some q := by simpa [peerAt,device] using found
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
          all_goals by_cases same : pid = owner
          all_goals first
            | (subst owner
               have peers : q = p := Option.some.inj (old.symm.trans stored)
               subst q
               first
               | (solve | exfalso; simp_all [PrevQueue.all])
               | exact ⟨pid,{p with refcount := p.refcount - 1},by simp [peerAt],member⟩)
            | exact ⟨owner,q,by simp [peerAt,Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert,same,old],member⟩
        · have zero : p.refcount = 0 := by omega
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,zero,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at run
          cases run

end Leanux.Proofs.WG.RetirementSecurity
