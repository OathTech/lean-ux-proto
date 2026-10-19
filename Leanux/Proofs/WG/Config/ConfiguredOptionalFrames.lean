import Leanux.Proofs.WG.Queues.BaseCoherenceCalls

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem base_frame_from_prefix {E α : Type} (observed : PrefixM E α)
    (action : Leanux.M α) (erase : ErasesPrefix observed action)
    (keeps : ∀ initial, PrefixPreserves
      (fun _ w => BaseCoherence.view w.wg = initial) (fun _ => True) observed) :
    SameView (fun w : World => BaseCoherence.view w.wg) action := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  obtain ⟨suffix,append,safe,post⟩ := keeps (BaseCoherence.view w.wg) w [] rfl
  have actual : (runPrefix observed w []).1 = .ok (result,v) :=
    (erase w []).trans run
  rw [actual] at post
  exact post

end Leanux.Proofs.WG.Config.OwnerConfiguration
