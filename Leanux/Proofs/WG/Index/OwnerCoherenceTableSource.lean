import Leanux.Proofs.WG.Index.OwnerCoherenceTableEffects
import Leanux.Proofs.WG.Index.Table
import Leanux.Proofs.WG.Index.Insert
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Actual guarded index removal is total for a present device. It preserves
hashed-owner coherence without requiring the removed owner to be resident. -/
theorem indexRemove_owner_coherence (owner : IndexOwner) (d : Device)
    (coherent : HashedOwnersCoherent d) :
    Campaign2.Returns (liftIndex (indexRemove owner)) (fun s => s.wg.device = some d)
      (fun _ s =>
        s.wg.device = some {d with indexTable := removeOwner owner d.indexTable} ∧
        HashedOwnersCoherent {d with indexTable := removeOwner owner d.indexTable}) := by
  intro g ambient device
  obtain ⟨value, final, after, run, effect⟩ := indexRemove_exact owner d g ambient device
  exact ⟨value, final, after, run, effect, hashedOwnersCoherent_remove d owner coherent⟩

/-- The current keypair-removal primitive is the keypair specialization of
indexRemove. It does not dereference the removed owner's stored peer word. -/
theorem keypairIndexRemove_owner_coherence (id : KeypairId) (d : Device)
    (coherent : HashedOwnersCoherent d) :
    Campaign2.Returns (liftIndex (indexRemove (.keypair id)))
      (fun s => s.wg.device = some d)
      (fun _ s =>
        s.wg.device = some {d with indexTable := removeOwner (.keypair id) d.indexTable} ∧
        HashedOwnersCoherent {d with indexTable := removeOwner (.keypair id) d.indexTable}) :=
  indexRemove_owner_coherence (.keypair id) d coherent

/-- Every normal insertion retains coherence when the newly published owner
is coherent initially. The original collision loop and all stopped outcomes
remain; no record readiness, uniqueness or allocation-freshness premise is added. -/
theorem indexInsert_owner_coherence (owner : IndexOwner) (d : Device)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d owner) :
    Campaign2.Ensures (liftIndex (indexInsert owner)) (fun s => s.wg.device = some d)
      (fun index s =>
        let table := {index, owner} :: removeOwner owner d.indexTable
        s.wg.device = some {d with indexTable := table} ∧
        HashedOwnersCoherent {d with indexTable := table}) := by
  intro g ambient index final after device run
  obtain ⟨effect, _⟩ := indexInsert_exact owner d g ambient index final after device run
  exact ⟨effect, hashedOwnersCoherent_insert d owner index coherent published⟩

/-- Actual replacement retains coherence and its exact Boolean/table effect.
The destination owner's coherence is supplied, not inferred from the replaced
handshake. Existing destination rows are allowed; owner uniqueness is not claimed. -/
theorem indexReplace_owner_coherence (pid : PeerId) (kp : KeypairId) (d : Device)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d (.keypair kp)) :
    Campaign2.Returns (liftIndex (indexReplaceHandshake pid kp))
      (fun s => s.wg.device = some d)
      (fun hashed s =>
        let updated := if hashed then {d with indexTable := replaceOwner pid kp d.indexTable} else d
        hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        s.wg.device = some updated ∧ HashedOwnersCoherent updated) := by
  intro g ambient device
  obtain ⟨hashed, final, after, run, value, effect⟩ := indexReplace_exact pid kp d g ambient device
  refine ⟨hashed, final, after, run, value, effect, ?_⟩
  cases hashed with
  | false => exact coherent
  | true => exact hashedOwnersCoherent_replace d pid kp coherent published

end Leanux.Proofs.WG.Index
