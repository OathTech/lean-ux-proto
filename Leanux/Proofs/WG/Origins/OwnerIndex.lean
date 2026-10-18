import Leanux.Proofs.WG.Origins.OwnerBounds
import Leanux.Proofs.WG.Origins.CurrentIndex
import Leanux.Proofs.WG.Queues.RxAdmissionCarrier

/-! The actual nullable owner acquisition and index scan preserve the receiving
owner carrier. The bounds come from existing source receipts; no initialized
history, affiliation invariant, or successful acquisition is assumed. -/
namespace Leanux.Proofs.WG.OwnerIndex
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

/-- A failed nullable get can clear a word. It cannot redirect one or move the
peer/key allocation frontiers, and every resident RX cell remains unchanged. -/
theorem acquireOwner_preserves (owner : IndexOwner) :
    Preserves Carrier (Affiliation.acquireOwner owner) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have acquisition := Affiliation.acquireOwner_acquisition owner w v result ambient finalAmbient hr
  have facts := acquisition.facts
  have frontiers (before after : Device) (hb : w.dev = some before) (ha : v.dev = some after) :
      after.nextPeer = before.nextPeer ∧ after.nextKeypairId = before.nextKeypairId := by
    have fields := facts.2
    simp only [Affiliation.view, hb, ha, Option.map_some, Option.some.injEq] at fields
    cases owner <;>
      exact ⟨congrArg Affiliation.State.nextPeer fields, congrArg Affiliation.State.nextKey fields⟩
  have rx := loan_rx (acquireOwner_loan owner w v result ambient finalAmbient hr)
  constructor
  · apply owners_retain hi.owners
      ((ProjectedAction.iff_run_ambient _ _ _).mp (Origins.acquireOwner_retains owner)
        w ambient result v finalAmbient hr)
    intro before after hb ha _
    exact Nat.le_of_eq (frontiers before after hb ha).1.symm
  · exact (acquisition_keyEffect acquisition).rxCompatible rx hi.compatible
  · intro after ha id pkt hp
    have oldRx : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
      simpa [rxView, ha, hp] using (congrFun (congrArg Prod.snd rx) id).symm
    obtain ⟨before, hb, oldPacket⟩ := Option.bind_eq_some_iff.mp oldRx
    rw [(frontiers before after hb ha).2]
    exact hi.rxKeys before hb id pkt oldPacket

/-- The original source scan includes every recorded decision and ordinary None
arm. Only actual native successful endpoints have an owner-carrier conclusion. -/
theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat) :
    Preserves Carrier (indexLookup kinds index) := by
  change Hoare (indexLookup kinds index) Carrier (fun _ => Carrier)
  have branchRule (decision : Decision) (value : Bool) :
      Preserves Carrier (branch decision value) :=
    hoare_liftAmbient (AmbientM.branch decision value) Carrier
  have stop {α : Type} (message : String) : Preserves Carrier (invariant message : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant message) Carrier
  have bucket : Preserves Carrier (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro w d table hi hd
    constructor
    · intro after ha slot key hk valid pid word
      have same : after = {d with indexTable := table} := Option.some.inj ha.symm
      subst after
      exact hi.owners d hd slot key hk valid pid word
    · intro after id pkt ha hp other key ho hk
      have same : after = {d with indexTable := table} := Option.some.inj ha.symm
      have same' : other = after := Option.some.inj (ho.symm.trans ha)
      subst other
      subst after
      exact hi.compatible d id pkt hd hp d key hd hk
    · intro after ha id pkt hp
      have same : after = {d with indexTable := table} := Option.some.inj ha.symm
      subst after
      exact hi.rxKeys d hd id pkt hp
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (index_material_head branch; exact branchRule _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact bucket)
    | (index_material_head Affiliation.acquireOwner; exact acquireOwner_preserves _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind (Q := fun _ => Carrier))
    | (index_material_head ForIn.forIn; apply list_view_spec id Carrier)
    | dsimp (config := {failIfUnchanged := true}) only
    | (run_tac do
        let ty ← (← Lean.Elab.Tactic.getMainGoal).getType
        unless ty.isForall do Lean.throwError "not a binder"
        Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
    | split

end Leanux.Proofs.WG.OwnerIndex
