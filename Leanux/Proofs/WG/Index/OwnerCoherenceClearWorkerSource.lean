import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerModel
import Leanux.Proofs.WG.Noise.Execution
import Leanux.Env

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Actual guarded named/head selection, before the queue write. -/
def clearWorkerSelect : Leanux.M PeerId := do
  let d ← getDev
  let some head := d.clearWorkQueue.head? | invariant "no queued clear work"
  match ← peekUnit .clearPeerWorker with
  | some unit => resolveUnit .clearPeerWorker unit d.clearWorkQueue
  | none => pure head

theorem runOneClearWorker_select_source : Env.runOneClearWorker = (do
    let pid ← clearWorkerSelect
    modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}
    Env.runWorker .clearPeerWorker (queuedExpiredZeroKeyMaterial pid)) := by
  unfold Env.runOneClearWorker clearWorkerSelect
  simp only [bind_assoc]
  apply bind_congr
  intro d
  cases d.clearWorkQueue.head? with
  | none => rfl
  | some head =>
    simp only [bind_assoc]
    apply bind_congr
    intro named
    cases named <;> rfl

/-- The real peek changes only Ambient and returns the pure entry selector word. -/
private theorem clearWorkerPeek_run (a : Ambient) :
    (AmbientM.peekUnit .clearPeerWorker).run a =
      .ok (clearWorkerUnit a.hidden,
        {a with hidden := a.hidden.map (fun rs => rs.dropWhile fun r => HiddenSite.passive r.site)}) := by
  cases hidden : a.hidden with
  | none =>
    simp [AmbientM.peekUnit, AmbientM.skipAmbient, hidden, clearWorkerUnit]
    rw [← hidden]
    rfl
  | some rs =>
    cases stripped : rs.dropWhile (fun r => HiddenSite.passive r.site) with
    | nil => simp [AmbientM.peekUnit, AmbientM.skipAmbient, hidden, stripped, clearWorkerUnit]; rfl
    | cons r rest =>
      simp [AmbientM.peekUnit, AmbientM.skipAmbient, hidden, stripped, clearWorkerUnit]
      split <;> rfl

/-- Normal selection agrees with the entry projection and really belongs to its
queue. Unknown units, missing devices and empty queues remain stopped paths. -/
theorem clearWorkerSelect_selected (initial final : World) (pid : PeerId)
    (run : clearWorkerSelect.run initial = .ok (pid,final)) :
    final.wg = initial.wg ∧ clearWorkerSelected (Campaign2.Product.snapshot initial) = some pid ∧
      ∃ d, initial.wg.dev = some d ∧ pid ∈ d.clearWorkQueue := by
  rw [clearWorkerSelect,StateT.run_bind] at run
  cases device : initial.wg.dev with
  | none =>
    have dev : (getDev : Leanux.M Device).run initial =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change (((getDev).run initial.wg).run initial.ambient >>= _) = _
      simp [getDev,device,invariant,AmbientM.invariant]
      rfl
    rw [dev] at run
    cases run
  | some d =>
    have dev : (getDev : Leanux.M Device).run initial = .ok (d,initial) := by
      change (((getDev).run initial.wg).run initial.ambient >>= _) = _
      simp [getDev,device]
      rfl
    rw [dev] at run
    dsimp only [Bind.bind,Except.bind] at run
    cases head : d.clearWorkQueue.head? with
    | none =>
      rw [head] at run
      cases run
    | some first =>
      rw [head] at run
      change ((do let named ← (peekUnit .clearPeerWorker : Leanux.M (Option Nat))
                  match named with
                  | some unit => resolveUnit .clearPeerWorker unit d.clearWorkQueue
                  | none => pure first).run initial) = _ at run
      let afterAmbient : Ambient := {initial.ambient with hidden := (initial.ambient.hidden.map (fun rs => rs.dropWhile fun r => HiddenSite.passive r.site))}
      let after : World := {initial with ambient := afterAmbient}
      have peek : (peekUnit .clearPeerWorker : Leanux.M (Option Nat)).run initial =
          .ok (clearWorkerUnit initial.ambient.hidden,after) := by
        change ((AmbientM.peekUnit .clearPeerWorker).run initial.ambient >>= _) = _
        rw [clearWorkerPeek_run]; rfl
      rw [StateT.run_bind,peek] at run
      cases named : clearWorkerUnit initial.ambient.hidden with
      | none =>
        simp only [named] at run
        cases run
        refine ⟨rfl,?_,d,rfl,List.mem_of_head? head⟩
        simp [clearWorkerSelected,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,device,head,named]
      | some unit =>
        simp only [named] at run
        change ((AmbientM.resolveUnit .clearPeerWorker unit d.clearWorkQueue).run after.ambient >>=
          fun (value,inputs) => Except.ok (value,{after with ambient := inputs})) = _ at run
        cases found : initial.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.clearPeerWorker.index) with
        | none =>
          simp [AmbientM.resolveUnit,after,afterAmbient,found] at run
          cases run
        | some item =>
          obtain ⟨address,worker,chosen⟩ := item
          by_cases queued : chosen ∈ d.clearWorkQueue
          · simp [AmbientM.resolveUnit,after,afterAmbient,found,queued] at run
            obtain ⟨rfl,rfl⟩ := run
            refine ⟨rfl,?_,d,rfl,queued⟩
            simp [clearWorkerSelected,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,device,head,named,found,queued]
          · simp [AmbientM.resolveUnit,after,afterAmbient,found,queued] at run
            cases run

end Leanux.Proofs.WG.Index
