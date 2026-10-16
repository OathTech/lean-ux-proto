import Leanux.Proofs.WG.Queues.TxDispositionCuts
import Leanux.Proofs.WG.Lifetimes.TxWorker

/-! Exact lifetime projection for the complete TX step, conditional on the
existing allocation invariant only at entry. All intermediate contracts are
discharged by the concrete lifetime helper proofs. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

theorem drop_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (drop pid item) (liftWGObserver (txDropPeekedPrefix pid)) := by
  unfold drop txDropPeekedPrefix
  simp only [liftWGObserver_bind]
  apply projectsPrefix_bind accessEvent id id (nativeAccess_project (getPeer_appends pid))
  intro p
  apply projectsPrefix_bind accessEvent id id (nativeAccess_project (getPeer_appends pid))
  intro q
  have he := projectsPrefix_bind accessEvent id id
    (f := fun _ : Unit => emitPrefix (.removed pid item)) (b := fun _ : Unit => pure ())
    (nativeAccess_project (setPeer_appends pid {p with txQueue := q.txQueue.dropPeeked}))
    (fun _ => cut_project accessEvent (.removed pid item) rfl)
  simpa only [bind_pure_unit, id] using he

theorem complete_access (pid : PeerId) (item : List SkbId) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (complete pid item) (liftWGObserver (createDataDonePrefix pid item)) :=
  projectsUnder_emit_bind _ rfl (access_projects
    ((createDataDonePrefix_preserves allocationAmbient allocationTx allocationSocket pid item).liftWGObserver))

def disposeAccess (pid : PeerId) (item : List SkbId) (key : KeypairId) : MixedM Bool := do
  for id in item do freeTxSkbPrefix id
  keypairPutPrefix (some key) false
  peerPutMixed (some pid)
  return true

theorem dispose_access (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProjectsPrefix accessEvent id (dispose pid item key) (liftWGObserver (disposeAccess pid item key)) := by
  unfold dispose disposeAccess
  simp only [liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_forIn]
  repeat' first
    | with_reducible exact nativeAccess_project (txFree_appends _)
    | with_reducible exact nativeAccess_project (keyPut_appends _ _)
    | with_reducible exact nativeAccess_project (peerPut_appends _)
    | exact project_pure _ _
    | with_reducible apply project_forIn accessEvent
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | (with_reducible intro x; try dsimp only [id])

theorem dispose_preserves (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (liftWGObserver (disposeAccess pid item key)) := by
  have native : StatePrefixPreserves (fun h w _ => AllocationInv h w)
      LifetimeEvent.Safe (disposeAccess pid item key) := by
    change StatePrefixEnsures _ _ _ (fun _ h w _ => AllocationInv h w)
    unfold disposeAccess
    repeat' first
      | (maintenance_head freeTxSkbPrefix; exact allocationTx.free _)
      | (maintenance_head keypairPutPrefix; exact allocationTx.put _ _)
      | (maintenance_head peerPutMixed; exact allocationAmbient.peerPut _)
      | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _
          (fun h w _ hi => allocationAmbient.safe h w hi) (fun _ _ _ hi => hi))
      | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _
          (fun _ h w _ => AllocationInv h w) _ (fun _ h w _ hi => allocationAmbient.safe h w hi))
      | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => AllocationInv h w))
      | maintenance_intro
  exact native.liftWGObserver

def bodyAccess (pid : PeerId) (first : Option (List SkbId)) : MixedM Bool := do
  let go ← andPrefix (liftWGPrefix (branch .txPacket first.isSome)) do
    let some f := first | liftWGPrefix (invariant "unreachable")
    let some h := f.head? | liftWGPrefix (invariant "an empty ring item")
    liftWGPrefix (branch .txNotUncrypted ((← getTxSkbPrefix h).state != .uncrypted))
  if !go then return false
  let some item := first | liftWGPrefix (invariant "unreachable")
  let some headId := item.head? | liftWGPrefix (invariant "an empty ring item")
  let head ← getTxSkbPrefix headId
  txDropPeekedPrefix pid
  if ← liftWGPrefix (branch .txCrypted (head.state == .crypted)) then createDataDonePrefix pid item
  disposeAccess pid item head.keypair

theorem body_access (pid : PeerId) (first : Option (List SkbId)) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (body pid first) (liftWGObserver (bodyAccess pid first)) := by
  cases first <;> (try (rename_i item; cases hh : item.head?))
  all_goals simp_all only [body, bodyAccess, andObs, andPrefix, liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift, apply_ite]
  all_goals repeat' first
    | with_reducible exact (nativeAccess_project (txGet_appends _)).under
    | with_reducible exact (drop_access _ _).under
    | with_reducible exact complete_access _ _
    | with_reducible exact (dispose_access _ _ _).under
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | exact (AmbientContracts.drop (allocationTx.get (fun _ => True) _)).liftWGObserver
    | exact (txDropPeekedPrefix_preserves allocationAmbient _).liftWGObserver
    | exact (createDataDonePrefix_preserves allocationAmbient allocationTx allocationSocket _ _).liftWGObserver
    | exact (AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)).liftWGObserver
    | exact (AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)).liftWGObserver
    | with_reducible exact PrefixPreserves.pure (fun h w hi => allocationAmbient.safe h w.wg hi) _
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem step_access (pid : PeerId) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (step pid) (liftWGObserver (txStepPrefix pid)) := by
  have hs : txStepPrefix pid = (do
      let (first, q) ← liftWGPrefix ((← getPeerMixed pid).txQueue.peek)
      modifyPeerKeysPrefix pid fun p => {p with txQueue := q}
      bodyAccess pid first) := by
    simp only [txStepPrefix, bodyAccess, disposeAccess, bind_assoc]
    rfl
  rw [hs]
  unfold step
  simp only [liftWGObserver_bind, liftWGObserver_lift]
  apply projectsUnder_bind (access_projects (AmbientContracts.drop
    (allocationAmbient.getPeer_frame (fun _ => True) pid)).liftWGObserver)
    (AmbientContracts.drop (allocationAmbient.getPeer_frame (fun _ => True) pid)).liftWGObserver
  intro p
  have hq := (AmbientContracts.drop (allocationAmbient.store (fun _ => True) _
    (prevQueuePeek_sameWGStore p.txQueue))).liftWGObserver
  simp only [liftWGObserver_lift] at hq
  apply projectsUnder_bind (projectsUnder_lift _ _) hq
  rintro ⟨first, q⟩
  have hu := AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient
    (fun _ => True) pid (fun p => {p with txQueue := q}) (fun _ => rfl))
  have hup := hu.liftWGObserver
  exact projectsUnder_bind (access_projects hup) hup (fun _ => body_access pid first)

end Leanux.Proofs.WG.Queues.TxDisposition
