import Leanux.Proofs.WG.Index.DumpCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

theorem socketCallOn_preserves (P : WGWorld → Prop) (fd : Nat) (body : Leanux.M Int)
    (hb : Preserves (fun w : World=>P w.wg) body) :
    Preserves (fun w : World=>P w.wg) (socketCallOn fd body) := by
  unfold socketCallOn
  apply preserves_bind (productFS_spec (fdget fd : FS.M Fd) _ (fun _ _ _ _ pre=>pre))
  intro f
  split
  · exact preserves_pure _
  · exact preserves_bind hb (fun ret=>
      preserves_bind (productFS_spec (fdput f : FS.M Unit) _ (fun _ _ _ _ pre=>pre))
        (fun _=>preserves_pure ret))

theorem netlinkRequest_preserves (P : WGWorld → Prop) (body : Leanux.M Int)
    (hb : Preserves (fun w : World=>P w.wg) body) :
    Preserves (fun w : World=>P w.wg) (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  apply preserves_bind
  · apply socketCallOn_preserves
    exact preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
      (fun _=>preserves_bind hb (fun ret=>
        preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
          (fun _=>preserves_pure ret)))
  intro ret
  exact preserves_bind (socketCallOn_preserves P _ _ (preserves_pure 0))
    (fun _=>preserves_pure ret)

end Leanux.Proofs.WG.Index.DumpCore
