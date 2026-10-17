import Leanux.Proofs.WG.Config.ReplacePeersRequestSource
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private abbrev requestPrefix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersPrefix
private abbrev requestSuffix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersSuffix

theorem observedReplacePeers_facts (selector : DeviceRef) :
    Campaign2.Product.Ensures (observedReplacePeers selector) (fun _ => True)
      (fun result _ => ∀ cut, result.1 = some cut → result.2 = 0 ∧ RemoveAllFacts cut) := by
  have hs : Noise.Product.Ensures (liftWG requestSuffix) (fun _ => True) (fun ret _ => ret = 0) := by
    intro w ret final pre run
    change Except.ok (0, _) = .ok (ret, final) at run
    exact (Prod.mk.inj (Except.ok.inj run)).1.symm
  intro w result final pre run
  change ((liftWG (requestPrefix selector)).run w >>= fun (selected, middle) =>
    (match selected with
    | .error e => pure (none, e)
    | .ok () => do
      let cut ← observedRemoveAll
      let ret ← liftWG requestSuffix
      pure (some cut, ret)).run middle) = .ok (result, final) at run
  cases hp : (liftWG (requestPrefix selector)).run w with
  | error err => rw [hp] at run; cases run
  | ok pair =>
    rcases pair with ⟨selected, middle⟩
    rw [hp] at run
    cases selected with
    | error e =>
      change Except.ok ((none, e), middle) = .ok (result, final) at run
      cases run
      intro cut impossible
      cases impossible
    | ok u =>
      cases u
      change (observedRemoveAll.run middle >>= fun (cut, marked) =>
        (liftWG requestSuffix).run marked >>= fun (ret, done) =>
          Except.ok ((some cut, ret), done)) = .ok (result, final) at run
      cases hm : observedRemoveAll.run middle with
      | error err => rw [hm] at run; cases run
      | ok pair =>
        rcases pair with ⟨cut, marked⟩
        rw [hm] at run
        dsimp only [Bind.bind, Except.bind] at run
        cases ht : (liftWG requestSuffix).run marked with
        | error err => rw [ht] at run; cases run
        | ok pair =>
          rcases pair with ⟨ret, done⟩
          rw [ht] at run
          cases run
          intro other equal
          cases equal
          exact ⟨hs marked ret done trivial ht,
            observedRemoveAll_facts middle cut marked trivial hm⟩

/-- Successful selection ensures that every normal full return exposes the
actual removal cut; it does not assert that cleanup returns. -/
theorem observedReplacePeers_selected (d : Device) :
    Campaign2.Product.Ensures (observedReplacePeers (byIndex d))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s.toSnapshot d)
      (fun result _ => ∃ cut, result = (some cut, 0) ∧ RemoveAllFacts cut) := by
  have hp : Noise.Ensures (requestPrefix (byIndex d))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun selected _ => selected = .ok ()) := by
    intro g ambient selected out after pre run
    obtain ⟨ret, current, remaining, executed, result, device⟩ :=
      ((returns_iff _ _ _).mpr (lookupInterface_index d)) g ambient pre
    subst ret
    change (((lookupInterface (byIndex d)).run g).run ambient >>= fun ((found, state), a) => _) = _ at run
    rw [executed] at run
    change Except.ok ((Except.ok (), _), _) = .ok ((selected, out), after) at run
    exact (Prod.mk.inj (Prod.mk.inj (Except.ok.inj run)).1).1.symm
  intro w result final pre run
  have facts := observedReplacePeers_facts (byIndex d) w result final trivial run
  change ((liftWG (requestPrefix (byIndex d))).run w >>= fun (selected, middle) =>
    (match selected with
    | .error e => pure (none, e)
    | .ok () => do
      let cut ← observedRemoveAll
      let ret ← liftWG requestSuffix
      pure (some cut, ret)).run middle) = .ok (result, final) at run
  have nativePre : w.wg.dev = some d ∧ selectsDevice w.wg d := pre
  cases hn : ((requestPrefix (byIndex d)).run w.wg).run w.ambient with
  | error err =>
    have lifted : (liftWG (requestPrefix (byIndex d))).run w = .error err := by
      change (Except.bind (((requestPrefix (byIndex d)).run w.wg).run w.ambient) _) = _
      rw [hn]; rfl
    rw [lifted] at run
    cases run
  | ok pair =>
    rcases pair with ⟨⟨selected, current⟩, remaining⟩
    have selectedOk := hp w.wg w.ambient selected current remaining nativePre hn
    subst selected
    have lifted : (liftWG (requestPrefix (byIndex d))).run w =
        .ok (.ok (), {w with wg := current, ambient := remaining}) := by
      change (Except.bind (((requestPrefix (byIndex d)).run w.wg).run w.ambient) _) = _
      rw [hn]; rfl
    rw [lifted] at run
    change (observedRemoveAll.run {w with wg := current, ambient := remaining} >>= fun (cut, marked) =>
      (liftWG requestSuffix).run marked >>= fun (ret, done) =>
        Except.ok ((some cut, ret), done)) = .ok (result, final) at run
    cases hm : observedRemoveAll.run {w with wg := current, ambient := remaining} with
    | error err => rw [hm] at run; cases run
    | ok pair =>
      rcases pair with ⟨cut, marked⟩
      rw [hm] at run
      dsimp only [Bind.bind, Except.bind] at run
      cases ht : (liftWG requestSuffix).run marked with
      | error err => rw [ht] at run; cases run
      | ok pair =>
        rcases pair with ⟨ret, done⟩
        rw [ht] at run
        cases run
        obtain ⟨rfl, correct⟩ := facts cut rfl
        exact ⟨cut, rfl, correct⟩

end Leanux.Proofs.WG.Config
