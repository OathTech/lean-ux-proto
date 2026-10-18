import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.CreatorIndexEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

/-- Reuse the exact original insertion effect after the actual dereference.
The supplied rule is only a pure device update; no operation is substituted.
NULL, absent-device, record and collision-exhaustion Stops remain original. -/
theorem creatorPublish_device_predicate (pid : PeerId) (D : Device → Prop)
    (stable : ∀ d index, D d → D {d with indexTable :=
      {index,owner := .handshake pid} :: removeOwner (.handshake pid) d.indexTable}) :
    Ensures (creatorPublish pid) (fun g => ∀ d, g.dev = some d → D d)
      (fun _ g => ∀ d, g.dev = some d → D d) := by
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → D d
  unfold creatorPublish
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr
      (Leanux.Proofs.Framing.indexOwner_peerDeref_preserves (.handshake pid) P)) ?_
  intro _ g ambient index out after pre run
  cases device : g.dev with
  | none =>
    rw [liftIndex_run_variant,device] at run
    cases run
  | some d =>
    obtain ⟨effect,_⟩ := indexInsert_exact (.handshake pid) d
      g ambient index out after device run
    intro actual found
    rw [effect] at found
    cases found
    exact stable d index (pre d device)

end Leanux.Proofs.WG.Index
