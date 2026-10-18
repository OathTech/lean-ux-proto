import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.Noise.ClearWorkerClaims
import Leanux.Proofs.WG.Noise.DriverTagLeafFrames

/-! Physical tag transport through actual dequeues and key-slot clearing. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Flush
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
universe u

abbrev tags (w : WGWorld) := responseTagMap w.dev

theorem prepare_tags (pid : PeerId) :
    SameView tags (Index.flushedSendPrepare pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases device : w.dev with
  | none =>
    simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases pendingFlag : p.handshakePending with
      | false =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,invariant,AmbientM.invariant] at run
        cases run
      | true =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,setPeer] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        funext target
        by_cases same : pid = target
        · subst target
          simp [tags,responseTagMap,device,peer]
        · simp [tags,responseTagMap,device,Std.TreeMap.getElem?_insert,same]

theorem keys_tags (pid : PeerId) : SameView tags (keypairsClear pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases device : w.dev with
  | none =>
    simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [keypairsClear,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨out,found,steps⟩ := keypairsClear_effect pid d p peer w ambient result v after device run
      change responseTagMap v.dev = responseTagMap w.dev
      rw [found,device]
      exact ClearWorker.clearRun_tagMap steps

theorem clearErase_tags (pid : PeerId) :
    SameView tags (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases run
  funext target
  simp [tags,responseTagMap,Option.bind_map,Function.comp_def]


end Leanux.Proofs.WG.Noise.DriverTags.Flush
