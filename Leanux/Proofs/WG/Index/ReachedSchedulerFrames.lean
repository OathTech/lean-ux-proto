import Leanux.Proofs.WG.Index.CryptCutSource
import Leanux.Proofs.WG.Index.ReachedReceiverSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedScheduler
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem work_fields (f : List PeerId→List PeerId) :
    SameView (fun w : WGWorld => (BaseCoherence.view w,ConfigurationIndex.fields w))
      (modifyDev fun d=>{d with txWorkQueue:=f d.txWorkQueue}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,
    ConfigurationIndex.fields,ConfigurationIndex.deviceFields,senderDeviceCell,Option.map_map,Function.comp_def]
  rfl

end Leanux.Proofs.WG.Index.ReachedScheduler
