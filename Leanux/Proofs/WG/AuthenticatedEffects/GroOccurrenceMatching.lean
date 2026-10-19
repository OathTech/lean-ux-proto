import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceSource

/-! Natural projection between occurrence-tagged GRO executions. Candidate
scope indices may project to neutral tokens; packet identity and bytes remain
unchanged, and every callback journal is projected exactly. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem normalList_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (callback : List Entry → PrefixM E Unit)
    (target : List Entry → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map (Entry.map scopeMap)))) (gro : Buffer) :
    ProjectsPrefix ρ (Buffer.map scopeMap) (normalListWith callback gro)
      (normalListWith target (gro.map scopeMap)) := by
  unfold normalListWith
  dsimp only [Buffer.map, Entry.map]
  apply projectsPrefix_ite
  · intro _
    exact projectsPrefix_pure ρ (Buffer.map scopeMap) _
  · intro _
    exact projectsPrefix_bind ρ id (Buffer.map scopeMap) (projects _)
      (fun _ => projectsPrefix_pure ρ (Buffer.map scopeMap) _)

theorem normalOne_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (callback : List Entry → PrefixM E Unit)
    (target : List Entry → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map (Entry.map scopeMap)))) (gro : Buffer) (entry : Entry) (segs : Nat) :
    ProjectsPrefix ρ (Buffer.map scopeMap) (normalOneWith callback gro entry segs)
      (normalOneWith target (gro.map scopeMap) (entry.map scopeMap) segs) := by
  unfold normalOneWith
  dsimp only [Buffer.map, Entry.map]
  split
  · simpa only [Buffer.map, Entry.map, List.map_append, List.map_cons, List.map_nil] using
      normalList_matching ρ scopeMap callback target projects
        {gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs}
  · simpa only [Buffer.map, Entry.map, List.map_append, List.map_cons, List.map_nil] using
      projectsPrefix_pure ρ (Buffer.map scopeMap)
        {gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs}

theorem receive_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (callback : List Entry → PrefixM E Unit)
    (target : List Entry → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map (Entry.map scopeMap)))) (gro : Buffer) (entry : Entry) :
    ProjectsPrefix ρ (Buffer.map scopeMap) (receiveWith liftPrefix callback gro entry)
      (receiveWith liftPrefix target (gro.map scopeMap) (entry.map scopeMap)) := by
  have pure_eq (g : Buffer) (a : Buffer) (he : (g.map scopeMap) = a) :
      ProjectsPrefix ρ (Buffer.map scopeMap) (pure g : PrefixM E Buffer) (pure a) := by
    rw [← he]
    exact projectsPrefix_pure _ _ _
  rcases gro with ⟨xs, count, held⟩
  cases held <;> try (rename_i old rest; cases rest)
  all_goals
    unfold receiveWith
    simp only [Buffer.map, Entry.map, List.map_cons, List.map_nil]
    repeat' first
      | contradiction
      | with_reducible exact normalOne_matching ρ scopeMap callback target projects _ _ _
      | with_reducible exact projectsPrefix_pure _ _ _
      | with_reducible exact projectsPrefix_lift _ _
      | with_reducible apply projectsPrefix_ite
      | with_reducible apply projectsPrefix_bind ρ (Buffer.map scopeMap) (Buffer.map scopeMap)
      | with_reducible apply projectsPrefix_bind ρ id (Buffer.map scopeMap)
      | (with_reducible intro x; try dsimp only)
      | (split; all_goals try simp_all only [])
    all_goals first
      | exact normalOne_matching ρ scopeMap callback target projects _ _ _
      | (apply pure_eq; simp only [Buffer.map, Entry.map, List.map_append, List.map_cons, List.map_nil])
      | exact fun _ _ => rfl

theorem flushAll_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (callback : List Entry → PrefixM E Unit)
    (target : List Entry → PrefixM F Unit)
    (projects : ∀ entries, ProjectsPrefix ρ id (callback entries)
      (target (entries.map (Entry.map scopeMap)))) (gro : Buffer) :
    ProjectsPrefix ρ id (flushAllWith callback gro)
      (flushAllWith target (gro.map scopeMap)) := by
  unfold flushAllWith
  apply projectsPrefix_bind ρ (Buffer.map scopeMap) id
  · apply projectsPrefix_forIn_map ρ (Buffer.map scopeMap) (Entry.map scopeMap)
    intro entry g
    exact projectsPrefix_bind ρ (Buffer.map scopeMap) (projectStep (Buffer.map scopeMap))
      (normalOne_matching ρ scopeMap callback target projects g entry 1)
      (fun g => projectsPrefix_pure ρ (projectStep (Buffer.map scopeMap)) (.yield g))
  · intro g
    apply projectsPrefix_bind ρ (Buffer.map scopeMap) id
      (normalList_matching ρ scopeMap callback target projects {g with held := []})
    intro _
    exact projectsPrefix_pure ρ id ()

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
