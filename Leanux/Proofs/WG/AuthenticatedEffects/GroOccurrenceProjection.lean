import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceSource

/-! Exact projection to the existing GRO source, with arbitrary projected
stack callbacks. This preserves their journals, state and every Stop prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem normalList_projects (ρ : E → Option F)
    (callback : List Entry → PrefixM E Unit)
    (target : List (List UInt8) → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map Entry.bytes))) (gro : Buffer) :
    ProjectsPrefix ρ Buffer.erase (normalListWith callback gro)
      (groNormalListPrefix target gro.erase) := by
  unfold normalListWith groNormalListPrefix
  dsimp only [Buffer.erase]
  apply projectsPrefix_ite
  · intro _
    exact projectsPrefix_pure ρ Buffer.erase _
  · intro _
    exact projectsPrefix_bind ρ id Buffer.erase (projects _)
      (fun _ => projectsPrefix_pure ρ Buffer.erase _)

theorem normalOne_projects (ρ : E → Option F)
    (callback : List Entry → PrefixM E Unit)
    (target : List (List UInt8) → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map Entry.bytes))) (gro : Buffer) (entry : Entry) (segs : Nat) :
    ProjectsPrefix ρ Buffer.erase (normalOneWith callback gro entry segs)
      (groNormalOnePrefix target gro.erase entry.bytes segs) := by
  unfold normalOneWith groNormalOnePrefix
  dsimp only [Buffer.erase]
  split
  · simpa only [Buffer.erase, List.map_append, List.map_cons, List.map_nil] using
      normalList_projects ρ callback target projects
        {gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs}
  · simpa only [Buffer.erase, List.map_append, List.map_cons, List.map_nil] using
      projectsPrefix_pure ρ Buffer.erase
        {gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs}

theorem receive_projects (ρ : E → Option F)
    (callback : List Entry → PrefixM E Unit)
    (target : List (List UInt8) → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map Entry.bytes))) (gro : Buffer) (entry : Entry) :
    ProjectsPrefix ρ Buffer.erase (receiveWith liftPrefix callback gro entry)
      (napiGroReceivePrefix target gro.erase entry.bytes) := by
  have pure_eq (g : Buffer) (a : GroState) (he : g.erase = a) :
      ProjectsPrefix ρ Buffer.erase (pure g : PrefixM E Buffer) (pure a) := by
    rw [← he]
    exact projectsPrefix_pure _ _ _
  rcases gro with ⟨xs, count, held⟩
  cases held <;> try (rename_i old rest; cases rest)
  all_goals
    unfold receiveWith napiGroReceivePrefix
    simp only [Buffer.erase, List.map_cons, List.map_nil]
    repeat' first
      | contradiction
      | with_reducible exact normalOne_projects ρ callback target projects _ _ _
      | with_reducible exact projectsPrefix_pure _ _ _
      | with_reducible exact projectsPrefix_lift _ _
      | with_reducible apply projectsPrefix_ite
      | with_reducible apply projectsPrefix_bind ρ Buffer.erase Buffer.erase
      | with_reducible apply projectsPrefix_bind ρ id Buffer.erase
      | (with_reducible intro x; try dsimp only)
      | (split <;> simp_all only)
    all_goals first
      | exact normalOne_projects ρ callback target projects _ _ _
      | (apply pure_eq; simp only [Buffer.erase, List.map_append, List.map_cons, List.map_nil])
      | exact fun _ _ => rfl

theorem flushAll_projects (ρ : E → Option F)
    (callback : List Entry → PrefixM E Unit)
    (target : List (List UInt8) → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map Entry.bytes))) (gro : Buffer) :
    ProjectsPrefix ρ id (flushAllWith callback gro)
      (napiGroFlushAllPrefix target gro.erase) := by
  unfold flushAllWith napiGroFlushAllPrefix
  apply projectsPrefix_bind ρ Buffer.erase id
  · apply projectsPrefix_forIn_map ρ Buffer.erase Entry.bytes
    intro entry g
    exact projectsPrefix_bind ρ Buffer.erase (projectStep Buffer.erase)
      (normalOne_projects ρ callback target projects g entry 1)
      (fun g => projectsPrefix_pure ρ (projectStep Buffer.erase) (.yield g))
  · intro g
    apply projectsPrefix_bind ρ Buffer.erase id
      (normalList_projects ρ callback target projects {g with held := []})
    intro _
    exact projectsPrefix_pure ρ id ()

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
