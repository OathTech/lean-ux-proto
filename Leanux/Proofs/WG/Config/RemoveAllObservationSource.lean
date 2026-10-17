import Leanux.Proofs.WG.Config.RemoveAllSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def observedRemoveAllMark (d : Device) : Leanux.M Campaign2.Product.Snapshot := do
  liftWG (removeAllMark d.peerList)
  Campaign2.Product.read

def observedRemoveAll : Leanux.M RemoveAllCall := do
  liftWG free
  let d ← liftWG getDev
  let afterMark ← observedRemoveAllMark d
  liftWG (removeAllCleanup d.peerList)
  return ⟨d, afterMark⟩

theorem observedRemoveAll_erase :
    (do let _ ← observedRemoveAll; pure ()) = liftWG peerRemoveAll := by
  have lift_bind {α β : Type} (a : WG.M α) (f : α → WG.M β) :
      liftWG (a >>= f) = (liftWG a >>= fun x => liftWG (f x)) := by
    funext w
    dsimp only [liftWG, StateT.run, StateT.bind, StateT.pure, StateT.map,
      Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
    cases run : a w.wg w.ambient with
    | error err => rfl
    | ok pair => rcases pair with ⟨⟨out, current⟩, after⟩; rfl
  have read_drop {α : Type} (a : Leanux.M α) :
      (do let _ ← Campaign2.Product.read; a) = a := rfl
  have unit_drop (a : Leanux.M Unit) : (do a; pure ()) = a := by
    funext entry
    change (a.run entry >>= fun out => Except.ok ((), out.2)) = a.run entry
    cases h : a.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  rw [peerRemoveAll_phases]
  simp only [observedRemoveAll, observedRemoveAllMark, lift_bind, bind_assoc,
    pure_bind, read_drop, unit_drop]

theorem observedRemoveAllMark_facts (d : Device) :
    Noise.Product.Ensures (observedRemoveAllMark d) (fun w => w.wg.dev = some d)
      (fun after _ => RemoveAllFacts ⟨d, after⟩) := by
  intro entry after final pre run pairs listed
  change ((liftWG (removeAllMark d.peerList)).run entry >>= fun (u, marked) =>
    Except.ok (Campaign2.Product.snapshot marked, marked)) = .ok (after, final) at run
  cases hm : ((removeAllMark d.peerList).run entry.wg).run entry.ambient with
  | error err =>
    have lifted : (liftWG (removeAllMark d.peerList)).run entry = .error err := by
      change (((removeAllMark d.peerList).run entry.wg).run entry.ambient >>= _) = _
      rw [hm]; rfl
    rw [lifted] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨u, markedWorld⟩, remaining⟩
    have lifted : (liftWG (removeAllMark d.peerList)).run entry =
        .ok (u, {entry with wg := markedWorld, ambient := remaining}) := by
      change (((removeAllMark d.peerList).run entry.wg).run entry.ambient >>= _) = _
      rw [hm]; rfl
    rw [lifted] at run
    cases run
    obtain ⟨marked, device, effect⟩ := removeAllMark_effect d.peerList d pairs listed
      entry.wg entry.ambient u markedWorld remaining pre hm
    exact ⟨marked, device, effect, deadPass_all_selected effect listed⟩

theorem observedRemoveAll_facts :
    Campaign2.Product.Ensures observedRemoveAll (fun _ => True) (fun cut _ => RemoveAllFacts cut) := by
  have trivial_call {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
    intro entry ret final pre run
    trivial
  have read : Noise.Product.Ensures (liftWG getDev) (fun _ => True)
      (fun d w => w.wg.dev = some d) := by
    intro entry d final pre run
    change (((getDev.run entry.wg).run entry.ambient) >>= _) = _ at run
    cases device : entry.wg.dev with
    | none =>
      have absent : (getDev.run entry.wg).run entry.ambient =
          .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp [getDev, device, invariant, AmbientM.invariant]
        rfl
      rw [absent] at run
      cases run
    | some actual =>
      have present : (getDev.run entry.wg).run entry.ambient = .ok ((actual, entry.wg), entry.ambient) := by
        simp [getDev, device]
        rfl
      rw [present] at run
      cases run
      exact device
  change Noise.Product.Ensures _ _ _
  unfold observedRemoveAll
  refine Noise.Product.ensures_bind _ _ (trivial_call _) ?_
  intro u
  refine Noise.Product.ensures_bind _ _ read ?_
  intro d
  refine Noise.Product.ensures_bind _ _ (observedRemoveAllMark_facts d) ?_
  intro after
  refine Noise.Product.ensures_bind _ _ (fun w result final pre run => pre) ?_
  intro u w result final pre run
  cases run
  exact pre

end Leanux.Proofs.WG.Config
