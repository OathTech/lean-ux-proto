import Leanux.Proofs.WG.Noise.DriverTagRunnerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration Origins.HistorySupport Std.Do

theorem initial_tags (net bare : Bool) : tagView (initialWG net bare) = emptyTags := by
  funext pid
  cases net <;> cases bare <;> rfl

theorem initial (trace : Trace) (w : World)
    (same : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
    StateInv emptyTags [] w := by
  have tags : tagView w.wg = emptyTags :=
    (congrArg (fun s : WGStoreView => responseTagMap s.dev) same).trans
      (initial_tags trace.net trace.bare)
  refine ⟨?_,by intro event member; cases member⟩
  change TagsRetained emptyTags (tagView w.wg)
  rw [tags]
  exact TagsRetained.refl _

theorem snapshot_tags (g : WGWorld) (ambient : Ambient) :
    (Campaign2.snapshot g ambient).tagAt = responseTagMap g.dev := by
  funext pid
  rfl


end Leanux.Proofs.WG.Noise.DriverTags.Initialized
