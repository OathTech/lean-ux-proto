import Leanux.Proofs.WG.Config.RemoveAllFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Every initially resident peer remains resident through the first pass.
Exactly the selected identities acquire deadness, including duplicate visits. -/
theorem deadPass_residents {d final : Device} {ids : List PeerId}
    (steps : DeadPassEffect d ids final) (other : PeerId) (p : Peer)
    (resident : d.peers[other]? = some p) :
    ∃ q, final.peers[other]? = some q ∧ q.isDead = (p.isDead || ids.contains other) := by
  induction steps generalizing p with
  | nil d => exact ⟨p, resident, by simp⟩
  | cons d pid rest selected removed final peer removal tail ih =>
    obtain ⟨next, nextResident, deadness⟩ := deadStep_residents d removed pid other selected p removal peer resident
    obtain ⟨q, finalResident, finalDead⟩ := ih next nextResident
    refine ⟨q, finalResident, ?_⟩
    rw [finalDead, deadness]
    have comparison : (other == pid) = decide (other = pid) := by
      by_cases same : other = pid
      · subst other; simp
      · have different : (other == pid) = false := beq_eq_false_iff_ne.mpr same
        simp [different, same]
    simp [Bool.or_assoc, comparison]

theorem deadPass_all_selected {d final : Device} {ids : List PeerId}
    (steps : DeadPassEffect d ids final) (resident : ListedResidents d ids) :
    ∀ pid ∈ ids, ∃ p, final.peers[pid]? = some p ∧ p.isDead = true := by
  intro pid member
  obtain ⟨p, found⟩ := resident pid member
  obtain ⟨q, finalResident, deadness⟩ := deadPass_residents steps pid p found
  exact ⟨q, finalResident, by simpa [member] using deadness⟩

end Leanux.Proofs.WG.Config
