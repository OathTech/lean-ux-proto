import Leanux.Proofs.WG.RetirementSecurity.Unpublication

/-! The clear worker's handshake reset and final peer payment cannot publish
key indices. This transports the three-slot unpublication result through the
literal worker rather than inferring index absence from empty peer slots. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Unpublication
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

theorem peer_put (pid : PeerId) (a b : Ambient)
    (run : ((peerPut (some pid)).run w).run a=.ok (((),v),b)) : Retains w v := by
  cases device:w.dev with
  | none=>
    simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
      invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    cases stored:d.peers[pid]? with
    | none=>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
        invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      have lift (action : IndexM Unit) : (liftM action : WG.M Unit)=liftIndex action := rfl
      by_cases positive:0<p.refcount
      · have nonzero:p.refcount≠0 := by omega
        by_cases final:p.refcount=1
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
        all_goals intro id before entries atIndex entry member
        all_goals simp only [indexAt,Option.map_some,Option.some.injEq] at atIndex
        all_goals subst entries
        all_goals apply before d.indexTable (by simp [indexAt,device]) entry
        all_goals first | exact member | exact (List.mem_filter.mp member).1
      · have zero:p.refcount=0 := by omega
        simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
          refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
          CounterWindow.branchCmp_run,device,stored,zero,
          StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
          CounterWindow.except_ok_bind,CounterWindow.except_pure,
          unsupported,AmbientM.unsupported] at run
        cases run

theorem worker (pid : PeerId) (p : Peer) (found : peerAt w pid=some p) (a b : Ambient)
    (run : ((queuedExpiredZeroKeyMaterial pid).run w).run a=.ok (((),v),b)) :
    SlotsCleared pid v ∧ (∀id∈SlotEntries p,Unpublished id v) := by
  have retired := (zero_worker_retirement pid w v a b run).1
  simp only [queuedExpiredZeroKeyMaterial,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,handshake,second,t,e,cleared,paid⟩ := run
  cases first
  cases second
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp (ClearedSlots.handshake_clear_points pid)
    w a () u c handshake
  have view := congrFun (congrArg (fun fields=>fields.2.2.1) points) pid
  have mapped : (peerAt u pid).map peerOwnership=some (peerOwnership p) := by
    simpa only [ownershipPointView,ownershipAt,found,Option.map_some] using view
  obtain ⟨q,resident,same⟩ := Option.map_eq_some_iff.mp mapped
  have slots := congrArg Prod.fst same
  have oldSlots : SlotEntries q=SlotEntries p := by
    unfold SlotEntries
    rw [show q.keypairNext=p.keypairNext from congrArg Prod.fst slots,
      show q.keypairPrevious=p.keypairPrevious from congrArg (fun fields=>fields.2.1) slots,
      show q.keypairCurrent=p.keypairCurrent from congrArg (fun fields=>fields.2.2) slots]
  have unpub := (clear pid q resident c e cleared).2.2
  exact ⟨retired,fun id member=>peer_put pid e b paid id (unpub id (oldSlots ▸ member))⟩

/-- Dequeue and recorded worker sections retain the original slot names;
clearing their index entries remains valid after the final peer payment. -/
theorem flushed (pid : PeerId) (p : Peer) (found : peerAt w pid=some p) (a b : Ambient)
    (run : ((runFlushedClearWork pid).run w).run a=.ok (((),v),b)) :
    SlotsCleared pid v ∧ (∀id∈SlotEntries p,Unpublished id v) := by
  have contract : Hoare (runFlushedClearWork pid) (fun w=>peerAt w pid=some p)
      (fun _ w=>SlotsCleared pid w ∧ ∀id∈SlotEntries p,Unpublished id w) := by
    unfold runFlushedClearWork
    apply hoare_bind _ _ (show Preserves (fun w=>peerAt w pid=some p)
        (modifyDev fun d=>{d with clearWorkQueue:=d.clearWorkQueue.erase pid}) from by
      unfold modifyDev
      apply hoare_modify
      intro w before
      simpa only [peerAt,Option.bind_map,Function.comp_def] using before)
    intro _
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker)) _)
    intro _
    apply hoare_bind _ _ (show Hoare (queuedExpiredZeroKeyMaterial pid) (fun w=>peerAt w pid=some p)
        (fun _ w=>SlotsCleared pid w ∧ ∀id∈SlotEntries p,Unpublished id w) from by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b before run
      cases result
      exact worker pid p before a b run)
    intro _
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker)) _)
    intro _
    exact preserves_pure ()
  exact (hoare_iff_run_ambient _ _ _).mp contract w a () v b found run

theorem dispatched (run : Env.runOneClearWorker.run w=.ok ((),v)) :
    ∃d pid,w.wg.dev=some d ∧ pid∈d.clearWorkQueue ∧ SlotsCleared pid v.wg ∧
      ∀p,d.peers[pid]?=some p→∀id∈SlotEntries p,Unpublished id v.wg := by
  obtain ⟨d,_,_,_,pid,workerAmbient,device,_,_,_,member,callback⟩ :=
    Queues.RxCredits.ClearWork.runOneClearWorker_selected w v run
  refine ⟨d,pid,device,member,(flushed_retirement pid w.wg v.wg workerAmbient v.ambient callback).1,?_⟩
  intro p found
  exact (flushed pid p (by simp [peerAt,device,found]) workerAmbient v.ambient callback).2

end Leanux.Proofs.WG.RetirementSecurity.Unpublication
