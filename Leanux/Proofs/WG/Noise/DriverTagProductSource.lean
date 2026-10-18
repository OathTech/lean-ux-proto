import Leanux.Proofs.WG.Noise.DriverTagProductFrames

/-! Embed a proved tag-silent old observation by executing it once with its
own journal. Only named atomic calls use this adapter; effectful callbacks
use the driver-tag observers instead. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def discard {E α : Type} (observer : PrefixM E α) : ProductObs α :=
  liftPrefix (fun w => (runPrefix observer w []).1)

theorem discard_eq {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) : discard observer = liftPrefix action := by
  apply congrArg liftPrefix
  funext w
  exact erases w []

theorem discard_erases {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) : ErasesPrefix (discard observer) action := by
  rw [discard_eq observer action erases]
  exact erasesPrefix_lift action

theorem discard_frame {E α : Type} (entry : TagMap)
    (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action)
    (frame : SameView (fun w : World => tagView w.wg) action) :
    PrefixPreserves (StateInv entry) ValidHistory (discard observer) := by
  rw [discard_eq observer action erases]
  exact lift_product_frame entry action frame

theorem discard_store {E α : Type} (entry : TagMap)
    (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) (frame : SameProductStore action) :
    PrefixPreserves (StateInv entry) ValidHistory (discard observer) := by
  rw [discard_eq observer action erases]
  exact lift_product_store entry action frame

theorem discard_native_frame {E α : Type} (entry : TagMap)
    (observer : PrefixM E α) (action : WG.M α)
    (erases : ErasesPrefix observer (liftWG action))
    (frame : SameView tagView action) :
    PrefixPreserves (StateInv entry) ValidHistory (discard observer) :=
  discard_frame entry observer (liftWG action) erases (native_product_frame action frame)

theorem discard_retained {E α : Type} (entry : TagMap)
    (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action)
    (frame : ∀ w value final, action.run w = .ok (value,final) →
      TagsRetained (tagView w.wg) (tagView final.wg)) :
    PrefixPreserves (StateInv entry) ValidHistory (discard observer) := by
  rw [discard_eq observer action erases]
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift action (safe entry)
  intro h w value final prior run
  exact ⟨prior.1.final_retained (frame w value final run),prior.2⟩

end Leanux.Proofs.WG.Noise.DriverTags

