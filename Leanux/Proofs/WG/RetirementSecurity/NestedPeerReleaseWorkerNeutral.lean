import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseWorkerFrames

/-! Exact neutral specialization of the selected clear worker. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem oneClear_lifted :
    (oneClearWith liftPrefix runWorkerPrefix
      (fun pid => liftWGObserver (clearWith lifted pid)) : PrefixM E Unit) =
      liftPrefix Env.runOneClearWorker := by
  let action : PrefixM E Unit := oneClearWith liftPrefix runWorkerPrefix
    (fun pid => liftWGObserver (clearWith lifted pid))
  have erased : ErasesPrefix action Env.runOneClearWorker :=
    oneClear_erases (fun pid => liftWGObserver_erases (by
      simpa only [clear_native] using clear_erases lifted_erases pid))
  have framed : HistoryFrame some action :=
    oneClear_frame some (fun pid => StateHistoryFrame.liftWGObserver
      (clear_frame some (lifted_frames some) pid))
  funext w h
  have history := framed w h
  simp only [List.filterMap_some] at history
  exact Prod.ext (erased w h) history

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
