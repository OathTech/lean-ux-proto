import Leanux.Proofs.WG.Noise.DriverTagDumpFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-! Source: the same generic contract covers each of the seven original dump
result types. The old observation executes once; only its irrelevant lifetime
journal is discarded. Native normal-return retention and all-outcome erasure
are separate claims. -/
theorem native (action : NetlinkDumpCall) (entry : TagMap) :
    Preserves (fun g => TagsRetained entry (tagView g)) action.original :=
  Config.DumpInvariant.call (contracts entry) action

theorem retained (action : NetlinkDumpCall) (g : WGWorld) (ambient : Ambient)
    (value : action.Result) (final : WGWorld) (after : Ambient)
    (run : (action.original.run g).run ambient = .ok ((value,final),after)) :
    TagsRetained (tagView g) (tagView final) :=
  (hoare_iff_run_ambient _ _ _).mp (native action (tagView g))
    g ambient value final after (TagsRetained.refl _) run

def observed (action : NetlinkDumpCall) : ProductObs action.Result :=
  discard (RxHistory.mixed (liftWGObserver action.observed))

theorem observed_erases (action : NetlinkDumpCall) :
    ErasesPrefix (observed action) (liftWG action.original) :=
  discard_erases _ _ (RxHistory.mixed_erases (liftWGObserver_erases action.erases))

theorem observed_preserves (entry : TagMap) (action : NetlinkDumpCall) :
    PrefixPreserves (StateInv entry) ValidHistory (observed action) :=
  discard_retained entry _ _
    (RxHistory.mixed_erases (liftWGObserver_erases action.erases))
    (native_product_retained action.original (retained action))

/-- No dump adds a tag receipt, including when the original call stops. -/
theorem observed_history (action : NetlinkDumpCall) (w : World)
    (history : List DriverTagEvent) :
    (runPrefix (observed action) w history).2 = history := rfl

end Leanux.Proofs.WG.Noise.DriverTags.Dump
