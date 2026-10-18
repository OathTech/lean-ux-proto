import Leanux.Proofs.WG.Noise.ClearWorkerSource
import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ClearWorkerDispatch
open Leanux Leanux.WG Noise Std.Do

/-- The actual section wrapper retains the whole clear-worker tag effect.
Residency and positive reference count are conclusions of normal completion. -/
theorem clearWorkerSection_tags (pid : PeerId) (d : Device) :
    Noise.Product.Ensures
      (Env.runWorker .clearPeerWorker (liftWG (queuedExpiredZeroKeyMaterial pid)))
      (fun w => w.wg.dev = some d)
      (fun _ w => ∃ p, d.peers[pid]? = some p ∧ 0 < p.refcount ∧
        ∀ target, responseTagMap w.wg.dev target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else responseTagMap (some d) target) := by
  have body : Noise.Product.Ensures (liftWG (queuedExpiredZeroKeyMaterial pid))
      (fun w => w.wg.dev = some d)
      (fun _ w => ∃ p, d.peers[pid]? = some p ∧ 0 < p.refcount ∧
        ∀ target, responseTagMap w.wg.dev target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else responseTagMap (some d) target) := by
    intro initial result final device run
    change (((queuedExpiredZeroKeyMaterial pid).run initial.wg).run initial.ambient >>=
      fun ((value,g),a) => Except.ok (value,{initial with wg := g,ambient := a})) = _ at run
    cases actual : ((queuedExpiredZeroKeyMaterial pid).run initial.wg).run initial.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,g⟩,a⟩ := pair
      rw [actual] at run
      cases run
      cases resident : d.peers[pid]? with
      | none =>
        simp [queuedExpiredZeroKeyMaterial,handshakeClear,IndexOwner.peerDeref,
          IndexOwner.peerWord,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at actual
        cases actual
      | some p =>
        exact ⟨p,rfl,ClearWorker.queuedClear_effect pid d p resident
          initial.wg initial.ambient result g a device actual⟩
  exact (Noise.Product.ensures_iff _ _ _).mpr
    (TimerDiscipline.runWorker_kernel_contract .clearPeerWorker _
      (fun g _ _ _ => g.dev = some d)
      (fun g _ _ _ => ∃ p, d.peers[pid]? = some p ∧ 0 < p.refcount ∧
        ∀ target, responseTagMap g.dev target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else responseTagMap (some d) target)
      ((Noise.Product.ensures_iff _ _ _).mp body))

/-- Original named/head selection, dequeue, section start, body and section
stop compose in the actual states. A duplicate queue occurrence is allowed. -/
theorem runOneClearWorker_tags (initial final : World) (result : Unit)
    (run : Env.runOneClearWorker.run initial = .ok (result,final)) :
    ∃ pid d p,
      Index.clearWorkerSelected (Campaign2.Product.snapshot initial) = some pid ∧
      initial.wg.dev = some d ∧ pid ∈ d.clearWorkQueue ∧
      d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      ∀ target, responseTagMap final.wg.dev target =
        if pid = target then
          if p.refcount = 1 then none else some HANDSHAKE_ZEROED
        else responseTagMap initial.wg.dev target := by
  rw [Index.runOneClearWorker_select_source,StateT.run_bind] at run
  cases selection : Index.clearWorkerSelect.run initial with
  | error stop => rw [selection] at run; cases run
  | ok pair =>
    obtain ⟨pid,middle⟩ := pair
    rw [selection] at run
    change ((do
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}
      Env.runWorker .clearPeerWorker (queuedExpiredZeroKeyMaterial pid) : Leanux.M Unit).run middle) = _ at run
    obtain ⟨same,selected,d,device,queued⟩ :=
      Index.clearWorkerSelect_selected initial middle pid selection
    have current : middle.wg.dev = some d := same ▸ device
    let removed : Device := {d with clearWorkQueue := d.clearWorkQueue.erase pid}
    let next : World := {middle with wg := {middle.wg with dev := some removed}}
    have dequeue : (modifyDev (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) :
        Leanux.M Unit).run middle = .ok ((),next) := by
      change Except.ok ((),{middle with wg := {middle.wg with dev := middle.wg.dev.map _}}) = _
      rw [current]
      rfl
    rw [StateT.run_bind,dequeue] at run
    obtain ⟨p,resident,positive,tags⟩ :=
      clearWorkerSection_tags pid removed next result final rfl run
    refine ⟨pid,d,p,selected,device,queued,resident,positive,?_⟩
    intro target
    simpa only [device,removed,responseTagMap,Option.bind_some] using tags target

end Leanux.Proofs.WG.Noise.ClearWorkerDispatch
