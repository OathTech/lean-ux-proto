import Leanux.Proofs.WG.Roaming.ResponseCallSource
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- The actual load and decay prefix can change lastUnderLoad and consume clock
records, but preserves the whole optional Device on every normal return. -/
theorem responseLoad_device (initial : Option Device) :
    Ensures responseLoad (fun g => g.dev = initial)
      (fun _ g => g.dev = initial) := by
  let P : WGWorld → Prop := fun g => g.dev = initial
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g a r out after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, device] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site value)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branchCmp site value lhs rhs)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P)) (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hmodify (last : Option Int64) :
      Ensures (modify fun g : WGWorld => {g with lastUnderLoad := last}) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g a r out after pre run; cases run
  change Ensures responseLoad P (fun _ => P)
  unfold responseLoad birthdateTest
  simp only [bind_assoc, pure_bind]
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hget
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hambient _
    | exact hmodify _
    | exact hstop _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | split

end Leanux.Proofs.WG.Roaming
