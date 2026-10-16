import Leanux.Proofs.Framing.WGHandshake
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Netlink
import Lean.Elab.Tactic

/-! Configuration-only device mutations retain the eleven WG-owned observations
outside their explicit device mask. Resident objects and allocator frontiers
remain visible; these normal-return contracts impose no Ambient restriction. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def configurationDevice (d : Device) : Device :=
  {d with staticIdentity := {}, cookieEncryptionKey := [], mac1Key := [], deviceUpdateGen := 0, fwmark := 0}

def configurationView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with dev := g.dev.map configurationDevice}

abbrev SameConfiguration (a : WG.M α) := SameView configurationView a

theorem modifyDev_configuration_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, configurationDevice (f d) = configurationDevice d) :
    ⦃fun w => ⌜P (configurationView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (configurationView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [configurationView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem setStaticIdentityPrivateKey_sameConfiguration (key : Key) :
    SameConfiguration (setStaticIdentityPrivateKey key) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => configurationView w = initial
  have read : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      exact hp
  have generated := ((generatePublic_sameWGWorld key).factor configurationView).wp (fun t => t = initial)
  change Preserves P (setStaticIdentityPrivateKey key)
  unfold setStaticIdentityPrivateKey
  apply preserves_bind read
  intro d
  apply preserves_bind
  · exact list_view_spec configurationView (fun t => t = initial) d.peerList () _
      (fun pid b => by
        simp only [requireNotPending, pure_bind]
        exact preserves_pure _)
  intro _
  apply preserves_bind generated
  rintro ⟨pub, has⟩
  exact modifyDev_configuration_spec (fun t => t = initial) _ (fun _ => rfl)

theorem cookiePrecomputeDeviceKeys_sameConfiguration :
    SameConfiguration cookiePrecomputeDeviceKeys := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => configurationView w = initial
  have read : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      exact hp
  change Preserves P cookiePrecomputeDeviceKeys
  unfold cookiePrecomputeDeviceKeys
  apply preserves_bind read
  intro d
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieDeviceHasIdentity d.staticIdentity.hasIdentity) P)
  intro b
  cases b <;> dsimp only
  all_goals simp only [pure_bind]
  all_goals exact modifyDev_configuration_spec (fun t => t = initial) _ (fun _ => rfl)

theorem netDevices_sameWGWorld : SameView (id : WGWorld → WGWorld) netDevices := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases hd : w.dev <;> simp [netDevices, hd] at hr
  all_goals cases hr; rfl

/-- Select only a visible source head; each selected rule is kernel checked. -/
elab "configuration_step" : tactic => Lean.Elab.Tactic.withMainContext do
  let t := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := t.getAppArgs
  let action ← if t.isAppOf ``Preserves then
    if args.size ≥ 1 then pure args[args.size - 1]! else Lean.throwError "missing action"
  else if t.isAppOf ``Hoare then
    if args.size ≥ 3 then pure args[args.size - 3]! else Lean.throwError "missing action"
  else Lean.throwError "not a preservation contract"
  let action := action.consumeMData
  let hb := Lean.mkIdent `hb
  let hn := Lean.mkIdent `hn
  let hi := Lean.mkIdent `hi
  if action.isAppOf ``Bind.bind then
    let xs := action.getAppArgs
    unless xs.size ≥ 2 do Lean.throwError "missing bind head"
    let head := xs[xs.size - 2]!.consumeMData
    if head.isAppOf ``Leanux.branch then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply preserves_bind ($hb _ _)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro b))
    else if head.isAppOf ``netDevices then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply preserves_bind $hn))
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro devs))
    else if head.isAppOf ``Leanux.invariant then
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply preserves_bind ($hi _)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro row))
    else Lean.throwError "unrecognized bind head"
  else if action.isAppOf ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preserves_pure _))
  else if action.isAppOf ``Leanux.invariant then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $hi _))
  else Lean.throwError "no source leaf rule"

theorem lookupInterface_sameWGWorld (ref : DeviceRef) :
    SameView (id : WGWorld → WGWorld) (lookupInterface ref) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => w = initial
  have hn : Preserves P netDevices := netDevices_sameWGWorld.wp (fun t => t = initial)
  have hb (d : Decision) (b : Bool) : Preserves P (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) P
  have hi {α : Type} (message : String) : Preserves P (invariant message : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant message) P
  change Preserves P (lookupInterface ref)
  unfold lookupInterface WG.orM
  repeat' first
    | configuration_step
    | split
    | simp +failIfUnchanged only [bind_assoc, pure_bind]

end Leanux.Proofs.Framing
