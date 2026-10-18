import Leanux.Proofs.WG.Noise.DriverTagSilentFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Silent
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues TimerDiscipline

theorem lift_preserves {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ initial, Preserves (Retained initial) action) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (liftWGPrefix action) := by
  apply lift_retained
  intro g ambient result final after run
  exact (hoare_iff_run_ambient _ _ _).mp (frame (tagView g))
    g ambient result final after (TagsRetained.refl _) run

theorem timerCallback_preserves (entry : TagMap) (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (timerCallback pid timer)) :=
  lift_preserves entry _ (fun initial => timerCallback_retained initial pid timer)

theorem txStep_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (txStep pid)) :=
  lift_preserves entry _ (fun initial => txStep_retained initial pid)

theorem decryptPrepare_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix RxWorkers.prepareSource) :=
  lift_preserves entry _ decryptPrepare_retained

theorem encryptPoll_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix TxRing.pollSource) :=
  lift_preserves entry _ encryptPoll_retained


end Leanux.Proofs.WG.Noise.DriverTags.Silent
