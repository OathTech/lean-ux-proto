import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Index.NewlinkFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem wgNewlink_tables : Ensures wgNewlink
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hdev (f : Device → Device)
      (safe : ∀ d, DeviceTablesSafe d → DeviceTablesSafe (f d)) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map f}), ambient) = _ at run
    cases run
    intro d present
    cases device : g.dev with
    | none => simp [device] at present
    | some original =>
      simp only [device, Option.map_some, Option.some.injEq] at present
      subst d
      exact safe original (pre original device)
  have hmodify (f : WGWorld → WGWorld) (same : ∀ g, (f g).dev = g.dev) :
      Ensures (modify f : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    intro d device
    exact pre d ((same g).symm.trans device)
  have hambient {α : Type} (a : AmbientM α) :
      Ensures (StateT.lift a : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant a TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    hambient (AmbientM.branch site value)
  have hpure (value : Int) : Ensures (pure value : WG.M Int) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hguard (failed : Bool) (next : WG.M Int) (rest : Ensures next TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if failed then unsupported "wg_newlink's unwinding after an allocation failure" else next)
        TablesSafeWG (fun _ => TablesSafeWG) := by
    cases failed with
    | false => exact rest
    | true =>
      intro g ambient result final after pre run
      cases run
  unfold wgNewlink
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hdev _ (fun _ h => h)) ?_
  intro _
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ((ensures_iff _ _ _).mpr cookieCheckerInit_tables) ?_
  intro _
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hdev _ (fun _ h => h)) ?_
  intro _
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ((ensures_iff _ _ _).mpr pubkeyHashtableAlloc_tables) ?_
  intro allocated
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
  intro failed
  cases failed with
  | true => exact hpure (-ENOMEM)
  | false =>
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .indexHashtableAlloc)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .allocWorkqueue)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .allocWorkqueue)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .allocWorkqueue)) ?_
    intro crypt
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hmodify _ (fun _ => rfl)) ?_
    intro _
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .packetQueueInit)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .packetQueueInit)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .packetQueueInit)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.skipCut allocCuts)) ?_
    intro _
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ((ensures_iff _ _ _).mpr ratelimiterInit_tables) ?_
    intro ret
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hambient (AmbientM.envOk .registerNetdevice)) ?_
    intro ok
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro failed
    refine hguard failed _ ?_
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
    · intro g ambient result final after pre run
      cases run
      exact pre
    · intro g
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hmodify _ (fun _ => rfl)) ?_
      intro _
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hdev _ (fun _ h => h)) ?_
      intro _
      exact ensures_bind _ _ (hambient (AmbientM.skipCutExactly .neighReachTime 2 allocCuts))
        (fun _ => hpure 0)

theorem wgSetup_tables_spec :
    ⦃fun _ => ⌜True⌝⦄ wgSetup ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨r, v, tail, execution, device⟩ := wgSetup_device g ambient pre
  rw [run] at execution
  cases execution
  intro d present
  rw [device] at present
  cases present
  exact setupDevice_safe

/-- Existing devices return EEXIST; otherwise setup initializes the table,
newlink preserves it, and a normally returning negative result removes it. -/
theorem wgCreate_tables : Ensures wgCreate
    TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure (value : Int) : Ensures (pure value : WG.M Int) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have rest : Ensures (do
      wgSetup
      let ret ← wgNewlink
      if ret < 0 then modify fun g => {g with dev := none}
      pure ret) (fun _ => True) (fun _ => TablesSafeWG) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr wgSetup_tables_spec) ?_
    intro _
    refine ensures_bind _ _ wgNewlink_tables ?_
    intro ret
    by_cases negative : ret < 0
    · simp only [negative, ite_true]
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => hpure ret)
      intro g ambient result final after pre run
      cases run
      intro d present
      cases present
    · simp only [negative, ite_false]
      exact hpure ret
  intro g ambient result final after pre run
  change (((if g.dev.isSome then pure (-EEXIST : Int) else do
    wgSetup
    let ret ← wgNewlink
    if ret < 0 then modify fun g => {g with dev := none}
    pure ret) : WG.M Int).run g).run ambient = _ at run
  cases present : g.dev.isSome with
  | true =>
    simp only [present, ite_true] at run
    exact hpure (-EEXIST) g ambient result final after pre run
  | false =>
    simp only [present, Bool.false_eq_true, ite_false] at run
    exact rest g ambient result final after trivial run

/-- The unchanged deletion prefix after the initial device-presence test.
The down operation and record consumers may stop. -/
def deletePrefix : WG.M Unit := do
  if (← getDev).running then wgDown
  skipCut allocCuts
  mayHaveSlept

theorem wgDelete_source : (wgDelete : WG.M Int) = (do
    if (← getWG).dev.isNone then return -ENODEV
    deletePrefix
    wgDestruct
    return 0) := by
  simp only [wgDelete, deletePrefix, bind_assoc, pure_bind]
  congr 1
  funext g
  split
  · rfl
  · congr 1
    funext d
    split <;> simp only [bind_assoc] <;> rfl

/-- Normal deletion leaves no device, including the already-absent ENODEV arm.
The original destructor supplies absence on the existing-device arm. -/
theorem wgDelete_absent : Ensures (wgDelete : WG.M Int) (fun _ => True)
    (fun _ g => g.dev = none) := by
  have rest : Ensures (do deletePrefix; wgDestruct; pure (0 : Int)) (fun _ => True)
      (fun _ g => g.dev = none) := by
    have hp : Ensures deletePrefix (fun _ => True) (fun _ _ => True) := by
      intro g ambient result final after pre run
      trivial
    refine ensures_bind _ _ hp ?_
    intro _
    refine ensures_bind _ _ wgDestruct_absent ?_
    intro _ g ambient result final after pre run
    cases run
    exact pre
  rw [wgDelete_source]
  intro g ambient result final after pre run
  change (((if g.dev.isNone then pure (-ENODEV : Int) else do
    deletePrefix
    wgDestruct
    pure (0 : Int)) : WG.M Int).run g).run ambient = _ at run
  cases device : g.dev with
  | none =>
    simp only [device, Option.isNone_none, ite_true] at run
    cases run
    exact device
  | some d =>
    simp only [device, Option.isNone_some, Bool.false_eq_true, ite_false] at run
    exact rest g ambient result final after pre run

end Leanux.Proofs.WG.Index
