import Leanux.Proofs.WG.RetirementSecurity.SessionHolders
import Leanux.Proofs.WG.RetirementSecurity.HolderClear
import Leanux.Proofs.WG.Queues.EnvClearDispatch

/-! Retirement at the actual zero-material work callback. Completion, rather
than elapsed time alone, is the scheduling boundary; outstanding packet
references may retain allocations after the three peer slots are cleared. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def slotFields (p : Peer) := (p.keypairNext,p.keypairPrevious,p.keypairCurrent)

theorem peerPut_slot_survivors (pid : PeerId) (w v : WGWorld) (d : Device) (p : Peer)
    (a b : Ambient) (device : w.dev = some d) (stored : d.peers[pid]? = some p)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    ∀ other q, peerAt v other = some q →
      ∃ old, peerAt w other = some old ∧ slotFields q = slotFields old := by
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
    all_goals intro other q found
    all_goals by_cases same : pid = other
    all_goals simp [peerAt,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,same] at found
    all_goals first
      | (subst other; subst q; exact ⟨p,by simp [peerAt,device,stored],rfl⟩)
      | exact ⟨q,by simpa [peerAt,device] using found,rfl⟩
  · have zero : p.refcount = 0 := by omega
    simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
      refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
      CounterWindow.branchCmp_run,device,stored,zero,
      StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      CounterWindow.except_ok_bind,CounterWindow.except_pure,
      unsupported,AmbientM.unsupported] at run
    cases run

theorem peerPut_slots (pid : PeerId) (word : Option PeerId) :
    Preserves (SlotsCleared pid) (peerPut word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b cleared run
  cases result
  cases word with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact cleared
  | some target =>
    cases device : w.dev with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[target]? with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
          invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        intro q found
        obtain ⟨old,resident,same⟩ := peerPut_slot_survivors target w v d p a b
          device stored run pid q found
        have empty := cleared old resident
        exact ⟨(congrArg Prod.fst same).trans empty.1,
          (congrArg (fun fields => fields.2.1) same).trans empty.2.1,
          (congrArg (fun fields => fields.2.2) same).trans empty.2.2⟩

theorem material_retains (same : Origins.view v = Origins.view w)
    (frontier : v.keypairCounter = w.keypairCounter) : Retains w v := by
  refine ⟨frontier,?_⟩
  intro id k found
  have cells := congrArg (fun view => view.bind fun fields => fields.2 id) same
  have equality : keyAt v id = keyAt w id := by
    simpa only [Origins.view,keyAt,Option.bind_map,Function.comp_def] using cells
  exact ⟨k,equality.symm.trans found,rfl⟩

theorem peerPut_retains (word : Option PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((peerPut word).run w).run a = .ok (((),v),b)) : Retains w v := by
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.peerPut_material word) w a () v b run
  have frontier := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.WGFrames.peerPut_sameSnapshot word) w a () v b run
  exact material_retains material (congrArg Keypairs.Snapshot.frontier frontier)

theorem handshakeClear_retains (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((handshakeClear pid).run w).run a = .ok (((),v),b)) : Retains w v := by
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.handshakeClear_material pid) w a () v b run
  have frontier := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.WGTransitions.handshakeClear_sameSnapshot pid) w a () v b run
  exact material_retains material (congrArg Keypairs.Snapshot.frontier frontier)

theorem zero_worker_retirement (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((queuedExpiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v := by
  rw [queuedExpiredZeroKeyMaterial,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,u,c,handshakeRun,tailRun⟩ := run
  cases result
  rw [MaterialOrigin.bind_ok_ambient] at tailRun
  obtain ⟨result,middle,middleAmbient,clearRun,putRun⟩ := tailRun
  cases result
  have cleared := (hoare_iff_run_ambient _ _ _).mp (clear_slots pid)
    u c () middle middleAmbient True.intro clearRun
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (peerPut_slots pid (some pid))
      middle middleAmbient () v b cleared putRun,
    (handshakeClear_retains pid w u a c handshakeRun).trans
      ((clear_retains pid u middle c middleAmbient clearRun).trans
        (peerPut_retains (some pid) middle v middleAmbient b putRun))⟩

theorem flushed_retirement_spec (pid : PeerId) (initial : WGWorld) :
    Hoare (runFlushedClearWork pid) (Retains initial)
      (fun _ w => SlotsCleared pid w ∧ Retains initial w) := by
  have dequeue : Preserves (Retains initial)
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    refine ⟨hi.counter,?_⟩
    intro id k found
    apply hi.keys id k
    cases device : w.dev with
    | none => simp [keyAt,device] at found
    | some d => simpa [keyAt,device] using found
  have callback : Hoare (queuedExpiredZeroKeyMaterial pid) (Retains initial)
      (fun _ w => SlotsCleared pid w ∧ Retains initial w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases result
    have retired := zero_worker_retirement pid w v a b run
    exact ⟨retired.1,hi.trans retired.2⟩
  unfold runFlushedClearWork
  apply hoare_bind _ _ dequeue
  intro _
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker))
    (Retains initial))
  intro _
  apply hoare_bind _ _ callback
  intro _
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker))
    (fun w => SlotsCleared pid w ∧ Retains initial w))
  intro _
  exact preserves_pure ()

theorem flushed_retirement (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v :=
  (hoare_iff_run_ambient _ _ _).mp (flushed_retirement_spec pid w)
    w a () v b (Retains.refl w) run

theorem dispatched_retirement (w v : World)
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ d pid, w.wg.dev = some d ∧ pid ∈ d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg := by
  obtain ⟨d,_,_,_,pid,beforeWorker,device,_,_,_,member,worker⟩ :=
    Queues.RxCredits.ClearWork.runOneClearWorker_selected w v run
  exact ⟨d,pid,device,member,flushed_retirement pid w.wg v.wg beforeWorker v.ambient worker⟩

end Leanux.Proofs.WG.RetirementSecurity
