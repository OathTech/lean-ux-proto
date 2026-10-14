import Leanux.Proofs.WG.Queues.TxDispositionCuts

/-! Exact lifetime projection for the complete TX step, conditional on the
existing allocation invariant only at entry. All intermediate contracts are
discharged by the concrete lifetime helper proofs. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

theorem drop_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (drop pid item) (txDropPeekedPrefix pid) := by
  unfold drop txDropPeekedPrefix
  apply projectsPrefix_bind accessEvent id id (access_project (getPeer_appends pid))
  intro p
  apply projectsPrefix_bind accessEvent id id (access_project (getPeer_appends pid))
  intro q
  have he := projectsPrefix_bind accessEvent id id
    (f := fun _ : Unit => emitPrefix (.removed pid item)) (b := fun _ : Unit => pure ())
    (access_project (setPeer_appends pid {p with txQueue := q.txQueue.dropPeeked}))
    (fun _ => cut_project accessEvent (.removed pid item) rfl)
  simpa only [bind_pure_unit, id] using he

theorem complete_access (pid : PeerId) (item : List SkbId) :
    ProjectsUnder AllocationInv accessEvent (complete pid item) (createDataDonePrefix pid item) :=
  projectsUnder_emit_bind _ rfl (access_projects
    (createDataDonePrefix_preserves allocationAmbient allocationTx allocationSocket pid item))

def disposeAccess (pid : PeerId) (item : List SkbId) (key : KeypairId) : MixedM Bool := do
  for id in item do freeTxSkbPrefix id
  keypairPutPrefix (some key) false
  peerPutMixed (some pid)
  return true

theorem dispose_access (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProjectsPrefix accessEvent id (dispose pid item key) (disposeAccess pid item key) := by
  unfold dispose disposeAccess
  repeat' first
    | with_reducible exact access_project (txFree_appends _)
    | with_reducible exact access_project (keyPut_appends _ _)
    | with_reducible exact access_project (peerPut_appends _)
    | exact project_pure _ _
    | with_reducible apply project_forIn accessEvent
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | (with_reducible intro x; try dsimp only [id])

theorem dispose_preserves (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (disposeAccess pid item key) := by
  unfold disposeAccess
  repeat' first
    | with_reducible exact allocationTx.free _
    | with_reducible exact allocationTx.put _ _
    | with_reducible exact allocationAmbient.peerPut _
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)

def bodyAccess (pid : PeerId) (first : Option (List SkbId)) : MixedM Bool := do
  let go ← andPrefix (liftPrefix (branch .txPacket first.isSome)) do
    let some f := first | liftPrefix (invariant "unreachable")
    let some h := f.head? | liftPrefix (invariant "an empty ring item")
    liftPrefix (branch .txNotUncrypted ((← getTxSkbPrefix h).state != .uncrypted))
  if !go then return false
  let some item := first | liftPrefix (invariant "unreachable")
  let some headId := item.head? | liftPrefix (invariant "an empty ring item")
  let head ← getTxSkbPrefix headId
  txDropPeekedPrefix pid
  if ← liftPrefix (branch .txCrypted (head.state == .crypted)) then createDataDonePrefix pid item
  disposeAccess pid item head.keypair

theorem body_access (pid : PeerId) (first : Option (List SkbId)) :
    ProjectsUnder AllocationInv accessEvent (body pid first) (bodyAccess pid first) := by
  cases first <;> (try (rename_i item; cases hh : item.head?))
  all_goals simp_all only [body, bodyAccess, andObs, andPrefix]
  all_goals repeat' first
    | with_reducible exact (access_project (txGet_appends _)).under
    | with_reducible exact (drop_access _ _).under
    | with_reducible exact complete_access _ _
    | with_reducible exact (dispose_access _ _ _).under
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact AmbientContracts.drop (allocationTx.get (fun _ => True) _)
    | with_reducible exact txDropPeekedPrefix_preserves allocationAmbient _
    | with_reducible exact createDataDonePrefix_preserves allocationAmbient allocationTx allocationSocket _ _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem step_access (pid : PeerId) :
    ProjectsUnder AllocationInv accessEvent (step pid) (txStepPrefix pid) := by
  have hs : txStepPrefix pid = (do
      let (first, q) ← liftPrefix ((← getPeerMixed pid).txQueue.peek)
      modifyPeerKeysPrefix pid fun p => {p with txQueue := q}
      bodyAccess pid first) := by
    simp only [txStepPrefix, bodyAccess, disposeAccess, bind_assoc]
    rfl
  rw [hs]
  unfold step
  apply projectsUnder_bind (access_projects (AmbientContracts.drop
    (allocationAmbient.getPeer_frame (fun _ => True) pid)))
    (AmbientContracts.drop (allocationAmbient.getPeer_frame (fun _ => True) pid))
  intro p
  apply projectsUnder_bind (projectsUnder_lift _ _)
    (AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (prevQueuePeek_sameKernel _)))
  rintro ⟨first, q⟩
  have hu := AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient
    (fun _ => True) pid (fun p => {p with txQueue := q}) (fun _ => rfl))
  exact projectsUnder_bind (access_projects hu) hu (fun _ => body_access pid first)

end Leanux.Proofs.WG.Queues.TxDisposition
