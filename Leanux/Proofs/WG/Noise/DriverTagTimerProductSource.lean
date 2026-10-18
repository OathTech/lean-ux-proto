import Leanux.Proofs.WG.Noise.DriverTagTimerProductFrames
import Leanux.Proofs.WG.Noise.DriverTagSilentSource

/-! Concrete timer dispatch and placeholder traversal contain no handshake
tag writer. The original guards, detachments and callback failures remain. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.TimerProduct
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do

theorem dispatch_native (entry : TagMap) (worker : Worker) (pid : PeerId)
    (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    Preserves (Retained entry) (timerDispatchUnit worker pid timer wheel prior) :=
  dispatch entry (Silent.timerCallback_retained entry) (Silent.delTimer entry)
    worker pid timer wheel prior

theorem placeholder_native (entry : TagMap) (j : UInt64) :
    Preserves (Retained entry) (RxHistory.placeholderTimerPassSource j) :=
  placeholder entry (Silent.timerCallback_retained entry) (Silent.delTimer entry) j

theorem lift_preserves {α : Type} (entry : TagMap) (action : Leanux.M α)
    (retains : ∀ initial, Preserves (Retained initial) action) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix action) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift action (safe entry)
  intro h w value final prior run
  have retained := (hoare_iff_run _ _ _).mp (retains (tagView w.wg))
    w value final (TagsRetained.refl _) run
  exact ⟨prior.1.final_retained retained,prior.2⟩

theorem dispatch_preserves (entry : TagMap) (worker : Worker) (pid : PeerId)
    (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (StateInv entry) ValidHistory
      (liftPrefix (timerDispatchUnit worker pid timer wheel prior)) :=
  lift_preserves entry _ (fun initial => dispatch_native initial worker pid timer wheel prior)

theorem placeholder_preserves (entry : TagMap) (j : UInt64) :
    PrefixPreserves (StateInv entry) ValidHistory
      (liftPrefix (RxHistory.placeholderTimerPassSource j)) :=
  lift_preserves entry _ (fun initial => placeholder_native initial j)

end Leanux.Proofs.WG.Noise.DriverTags.TimerProduct

