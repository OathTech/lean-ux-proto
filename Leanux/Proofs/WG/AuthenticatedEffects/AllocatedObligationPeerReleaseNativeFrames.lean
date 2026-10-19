import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCreate

/-! The original counted peer-release cut removes only an empty native TX
queue. Its packet store and allocation frontier are unchanged, including at
the cut before a final-release timer check can stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations Queues.RxCredits
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem cut_queues (target : Option PeerId) : SameView txQueueContents (releaseCut target) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases target with
  | none =>
    simp [releaseCut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    rfl
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [releaseCut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[pid]? with
      | none =>
        simp [releaseCut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
          invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [releaseCut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lift,liftIndex_run,CounterWindow.branch_run,CounterWindow.branchCmp_run,
              device,stored,positive,nonzero,final,StateT.run_bind,StateT.run_pure,
              StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals
            try simp [Except.map,StateT.run_map,StateT.run_modify,
              CounterWindow.except_ok_bind,CounterWindow.except_pure] at run
          all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
          all_goals funext owner
          all_goals by_cases same : pid = owner
          all_goals first
            | (subst owner; simp_all [txQueueContents,handoffTxView,PrevQueue.all])
            | simp [txQueueContents,handoffTxView,device,Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert,same]
        · have zero : p.refcount = 0 := by omega
          simp [releaseCut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,zero,StateT.run_bind,
            StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
            CounterWindow.except_pure,unsupported,AmbientM.unsupported] at run
          cases run

/-- Original cut ownership and packet-allocation bounds survive both the
nonfinal decrement and the counted final erase, before its suffix runs. -/
theorem cut_ownership (target : Option PeerId)
    (covered : TxCoverage locals w) (unique : TxInventory locals w) (bounded : Packets.Inv w)
    (a b : Ambient) (run : ((releaseCut target).run w).run a = .ok ((value,v),b)) :
    TxCoverage locals v ∧ TxInventory locals v ∧ Packets.Inv v := by
  have geometry := (ProjectedAction.iff_run_ambient _ _ _).mp (release_packet_geometry target)
    w a value v b run
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (cut_queues target)
    w a value v b run
  refine ⟨covered.cells (congrArg Prod.snd geometry) queues,
    unique.queueContents queues (congrArg Prod.snd geometry),?_⟩
  unfold Packets.Inv
  change Bounded (StagingOccurrences.geometry v).1
  rw [geometry]
  exact bounded

theorem finish_store (pid : PeerId) (p : Peer) : SameWGStore (releaseFinish pid p) := by
  intro initial
  change Preserves (fun w => wgStoreView w = initial) _
  unfold releaseFinish retirePeerUnits modifyAmbient
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | (allocation_release_head modify; apply hoare_modify; intro w before; exact before)
    | allocation_release_step

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
