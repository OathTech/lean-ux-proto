import Leanux.Proofs.WG.Index.DumpWrapperSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

theorem dispatchGet_entry (cs : Ledger) (loans : Reservations) (ref : DeviceRef) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (dispatch (.wgGet ref)) := by
  simp only [dispatch]
  apply netlinkRequest_preserves
  apply preserves_bind (LifecycleEnvironment.lift_entry cs loans _ (device_entry cs loans ref))
  intro result
  cases result with
  | error e => exact preserves_pure e
  | ok device =>
    exact preserves_bind (productAmbient_spec
      (modify fun w=>{w with extraOut:=[("device",device)]}) _ (fun _ _ pre=>pre))
      (fun _=>preserves_pure 0)

theorem dispatchRecv_entry (cs : Ledger) (loans : Reservations) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (dispatch .wgGetRecv) := by
  simp only [dispatch]
  apply socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply preserves_bind (LifecycleEnvironment.lift_entry cs loans _ (receive_entry cs loans DUMP_FD))
  intro result
  cases result with
  | none => exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre)
  | some messages =>
    apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
    intro _
    split
    · exact preserves_bind (productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre))
        (fun _=>preserves_bind (productAmbient_spec
          (modify fun w=>{w with extraOut:=[("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]})
          _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0))
    · exact preserves_bind (productAmbient_spec
          (modify fun w=>{w with extraOut:=[("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]})
          _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0)

theorem dispatchStart_entry (cs : Ledger) (loans : Reservations) (ref : DeviceRef) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg)
      (dispatch (.wgGetStart ref)) := by
  let P := fun w : World=>ConfigurationIndex.Entry cs loans w.wg
  have tail : Preserves P (do
      liftWG (netlinkDumpStart DUMP_FD ref)
      skipCut allocCuts
      pure (0 : Int) : Leanux.M Int) :=
    preserves_bind (LifecycleEnvironment.lift_entry cs loans _ (start_entry cs loans DUMP_FD ref))
      (fun _=>preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
        (fun _=>preserves_pure 0))
  have getter : Hoare (liftWG (getNlSock DUMP_FD)) P
      (fun sock w=>P w ∧sock=socketAt DUMP_FD w.wg) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w sock v pre run
    change Except.ok (socketAt DUMP_FD w.wg,w)=Except.ok (sock,v) at run
    cases run
    exact ⟨pre,rfl⟩
  simp only [dispatch]
  apply socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply hoare_bind _ _ getter
  intro sock
  split
  · apply hoare_bind _ _ (productAmbient_spec
      (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)
      (fun w : World=>P w ∧sock=socketAt DUMP_FD w.wg) (fun _ _ pre=>pre))
    intro _
    apply hoare_bind _ _ (show Hoare (liftWG (setNlSock DUMP_FD {sock with bound:=true}))
      (fun w : World=>P w ∧sock=socketAt DUMP_FD w.wg) (fun _=>P) from by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v pre run
      change Except.ok ((),{w with wg:=writeSocket DUMP_FD {sock with bound:=true} w.wg})=
        Except.ok (x,v) at run
      cases run
      rw [pre.2]
      exact socket_bound_entry cs loans DUMP_FD w.wg pre.1)
    intro _
    exact tail
  · exact hoare_consequence tail (fun _ pre=>pre.1) (fun _ _ pre=>pre)

end Leanux.Proofs.WG.Index.DumpCore
