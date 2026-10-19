import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterRouting

/-! Native boundary frames hide a carrier history only after its paired
entry has been obtained. Metadata operations preserve that same witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem Boundary.wg_store (hi : Boundary w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : Boundary v := by
  obtain ⟨h,cs,entry⟩ := hi
  exact ⟨h,cs,HolderEntryDispatch.wg_store entry.1 same,entry.2.store same⟩

namespace NativeFrames

theorem product (action : Leanux.M α) (same : SameProductStore action) :
    Preserves Boundary action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact hi.wg_store (congrArg (fun p : ProductStore43 => p.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run))

theorem fs (action : FS.M α) : Preserves Boundary (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ hi => hi.wg_store rfl)

theorem seccomp (action : Seccomp.M α) : Preserves Boundary (liftSeccomp action) :=
  productSeccomp_spec action _ (fun _ _ _ _ hi => hi.wg_store rfl)

theorem ambient (action : AmbientM α) : Preserves Boundary (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi.wg_store rfl)

theorem world (f : World → World)
    (same : ∀ w,wgStoreView (f w).wg=wgStoreView w.wg) : Preserves Boundary (modify f : Leanux.M Unit) :=
  hoare_modify f (fun w hi => hi.wg_store (same w))

theorem editAmbient (f : Ambient → Ambient) : Preserves Boundary (modifyAmbient f : Leanux.M Unit) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi.wg_store rfl

theorem socket (fd : Nat) (action : Leanux.M Int) (keeps : Preserves Boundary action) :
    Preserves Boundary (socketCallOn fd action) :=
  Frames.socket _ (fun _ _ same hi => hi.wg_store same) fd action keeps

theorem route : Preserves Boundary Env.routeIntoWg0 :=
  Frames.boundary _ _ (RxHistory.audit_erases routeIntoWg0Audit_erases) (fun _ => Controls.route)

theorem observe : Preserves Boundary Env.observe := by
  rw [Environment.observe_eq]
  exact preserves_bind Closed.idle_boundary (fun _ => product _ observeTail_sameKernel)

theorem observe_dispatch : Preserves Boundary (Leanux.dispatch .wgObserve) := by
  unfold Leanux.dispatch
  apply preserves_bind observe
  intro result
  apply preserves_bind (editAmbient _)
  intro _
  exact socket _ _ (preserves_pure _)

end NativeFrames
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
