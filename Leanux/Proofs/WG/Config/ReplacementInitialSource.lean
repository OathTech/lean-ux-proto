import Leanux.Proofs.WG.Config.ReplacementInitialEffects
import Leanux.Proofs.WG.Config.ReplacePeersRequestClaims
import Leanux.Proofs.WG.Config.RequestModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original free run establishes the captured post-free relation. The
observer still executes both removal passes and their actual failures. -/
theorem observedRemoveAll_cleared (d : Device) (t4 t6 : AllowedIps.Tree)
    (hi : AllowedIps.RoutingInvariant d t4 t6) :
    Campaign2.Product.Ensures observedRemoveAll (fun s => s.wg.device = some d)
      (fun cut _ => AllowedIps.Cleared d cut.afterFree) := by
  have hf : Noise.Product.Ensures (liftWG WG.free) (fun w => w.wg.dev = some d)
      (fun _ w => ∃ out, w.wg.dev = some out ∧ AllowedIps.Cleared d out) := by
    intro w result final device run
    rw [Framing.liftWG_run] at run
    cases native : (WG.free.run w.wg).run w.ambient with
    | error err => simp only [native, Except.map] at run; cases run
    | ok pair =>
      obtain ⟨⟨u,g⟩,ambient⟩ := pair
      cases u
      simp only [native, Except.map] at run
      cases run
      obtain ⟨out,view,hc⟩ := AllowedIps.free_endpoint w.wg g w.ambient ambient d device t4 t6 hi native
      exact ⟨out, congrArg Framing.WGStoreView.dev view, hc⟩
  have any {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) :=
    fun _ _ _ _ _ => trivial
  change Noise.Product.Ensures _ _ _
  unfold observedRemoveAll
  refine Noise.Product.ensures_bind _ _ hf ?_
  intro u entry result final pre run
  obtain ⟨out, device, hc⟩ := pre
  have read : (liftWG getDev).run entry = .ok (out, entry) := by
    simp [Framing.liftWG_run, getDev, device]
    rfl
  change ((liftWG getDev).run entry >>= fun (current,next) =>
    ((do
      let afterMark ← observedRemoveAllMark current
      liftWG (removeAllCleanup current.peerList)
      pure (⟨current,afterMark⟩ : RemoveAllCall))).run next) = _ at run
  rw [read] at run
  have tail : Noise.Product.Ensures (do
      let afterMark ← observedRemoveAllMark out
      liftWG (removeAllCleanup out.peerList)
      pure (⟨out,afterMark⟩ : RemoveAllCall))
      (fun _ => True) (fun cut _ => cut.afterFree = out) := by
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro afterMark
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro u w cut final _ hr
    cases hr
    rfl
  have same := tail entry result final trivial run
  rw [same]
  exact hc

private abbrev replaceInitialPrefix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersPrefix

/-- Successful device selection reaches removal with exactly the request's
generation increment, leaving every other Device field unchanged. -/
theorem replacePeersPrefix_generation (d : Device) :
    Noise.Ensures (replaceInitialPrefix (byIndex d))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun ret g => ret = .ok () ∧ g.dev = some (requestGeneration d)) := by
  intro g ambient selected out after pre run
  obtain ⟨ret,current,remaining,executed,result,device⟩ :=
    ((returns_iff _ _ _).mpr (lookupInterface_index d)) g ambient pre
  subst ret
  change (((lookupInterface (byIndex d)).run g).run ambient >>= fun ((found,state),a) => _) = _ at run
  rw [executed] at run
  simp [branch, AmbientM.branch, modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  exact ⟨rfl, by simp [requestGeneration, device]⟩

end Leanux.Proofs.WG.Config
