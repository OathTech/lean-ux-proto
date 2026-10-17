import Leanux.Proofs.Framing.Product
import Leanux.Syscalls

/-! Closing fixture holders composes actual filesystem actions at the runner
boundary. Namespace cleanup still occurs in the enclosing environment step. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

namespace SyscallFrames
theorem netnsClose_sameWGStore :
    SameView (fun w : World => wgStoreView w.wg) netnsClose := by
  let view := fun w : World => wgStoreView w.wg
  have fs {α : Type} (a : FS.M α) :
      SameView view (MonadLift.monadLift a : Leanux.M α) :=
    fun initial => productFS_spec a _ (fun _ _ _ _ h => h)
  have ambient {α : Type} (a : AmbientM α) :
      SameView view (MonadLift.monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a _ (fun _ _ h => h)
  have route : SameView view (getRouting : Leanux.M Net.Routing) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have fixture : SameView view getEnv := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have closeAll : SameView view (do
      for fd in [INJECT_FD, LISTEN6_FD, LISTEN4_FD, PIN_FD] do
        let ret ← sysClose fd
        if ret != 0 then invariant s!"close({fd}) of a fixture holder returned {ret}"
        taskWorkRun
      pure 0 : Leanux.M Int) := by
    apply SameView.bind
    · intro initial
      apply list_view_spec view (fun s => s = initial)
      intro fd accumulator
      apply preserves_bind (fs (sysClose fd) initial)
      intro ret
      dsimp only
      split
      · exact preserves_bind (ambient (AmbientM.invariant _) initial)
          (fun _ => preserves_bind (fs taskWorkRun initial) (fun _ => preserves_pure _))
      · exact preserves_bind (fs taskWorkRun initial) (fun _ => preserves_pure _)
    · intro _
      exact SameView.pure _ _
  have holders : SameView view (do
      if (← getEnv).netnsCHolders.isEmpty then unsupported "wg_netns_close twice"
      for fd in [INJECT_FD, LISTEN6_FD, LISTEN4_FD, PIN_FD] do
        let ret ← sysClose fd
        if ret != 0 then invariant s!"close({fd}) of a fixture holder returned {ret}"
        taskWorkRun
      pure 0 : Leanux.M Int) := by
    apply SameView.bind fixture
    intro e
    dsimp only
    split
    · exact SameView.bind (ambient (AmbientM.unsupported "wg_netns_close twice")) (fun _ => closeAll)
    · exact closeAll
  unfold netnsClose
  apply SameView.bind route
  intro r
  dsimp only
  split
  · exact SameView.bind
      (ambient (AmbientM.unsupported "wg_netns_close outside the foreign-creator fixture"))
      (fun _ => holders)
  · exact holders

theorem netnsClose_spec (P : WGStoreView → Prop) :
    ⦃fun w : World => ⌜P (wgStoreView w.wg)⌝⦄ netnsClose
    ⦃⇓? _ w => ⌜P (wgStoreView w.wg)⌝⦄ := netnsClose_sameWGStore.wp P

end SyscallFrames
end Leanux.Proofs.Framing
