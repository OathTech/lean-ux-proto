import Leanux.Proofs.WG.Queues.RxPollTags
import Leanux.Proofs.Logged.ProjectsPrefix

/-! The tagged poll and the removal-only poll observe the same original
execution, including actual stack callbacks and every failure prefix. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def removedId? : GroEvent → Option SkbId
  | .removed _ id => some id
  | _ => none

theorem removedId_eq (h : List GroEvent) :
    h.filterMap removedId? = (removedTags h).map Prod.snd := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp_all [removedTags, removedId?, List.filterMap_cons]

theorem dropGro_projects (pid n id : Nat) :
    ProjectsPrefix removedId? (fun x => x) (dropGroPrefix pid n id) (dropRxPrefix pid id) := by
  intro w h
  simp only [dropGroPrefix, dropRxPrefix, runPrefix_bind, runPrefix_lift]
  cases (liftWG (dropRxQueue pid)).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨u, v⟩
    cases u
    simp [List.filterMap_append, removedId?, Except.map]

theorem consumeGro_projects (pid n id : Nat) (pkt : RxPacket) (endpoint : Endpoint) :
    ProjectsPrefix removedId? (Option.map GroEntry.bytes) (consumeGro pid n id pkt endpoint)
      (liftPrefix (liftWG (consumeDataDone pid pkt endpoint))) := by
  intro w h
  rw [consumeGro_run]
  simp only [runPrefix_lift]
  cases (liftWG (consumeDataDone pid pkt endpoint)).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes <;> simp [List.filterMap_append, removedId?, Except.map]

theorem flushGro_projects (xs : List GroEntry) :
    ProjectsPrefix removedId? id (flushGro xs)
      (liftPrefix ((xs.map GroEntry.bytes).forM Leanux.Env.deliverInner)) := by
  intro w h
  apply Prod.ext
  · have he := flushGro_erases xs w h
    simp only [runPrefix_lift]
    rw [he]
    cases ((xs.map GroEntry.bytes).forM Leanux.Env.deliverInner).run w <;> rfl
  · obtain ⟨visited, remaining, he, hh, hok⟩ := flushGro_prefix xs w h
    simp only [runPrefix_lift]
    rw [hh]
    have hn : visited.filterMap (fun _ => (none : Option SkbId)) = [] := by
      induction visited <;> simp_all
    simp [List.filterMap_append, List.filterMap_map, Function.comp_def, removedId?, hn]

theorem groNormalList_projects (g : TaggedGro) :
    ProjectsPrefix removedId? TaggedGro.erase (groNormalListTagged g)
      (groNormalListPrefix (fun bytes => liftPrefix (bytes.forM Leanux.Env.deliverInner)) g.erase) := by
  unfold groNormalListTagged groNormalListPrefix
  dsimp only [TaggedGro.erase]
  apply projectsPrefix_ite
  all_goals intro h
  · exact projectsPrefix_pure removedId? TaggedGro.erase _
  · exact projectsPrefix_bind removedId? id TaggedGro.erase (flushGro_projects _)
      (fun _ => projectsPrefix_pure removedId? TaggedGro.erase _)

theorem groNormalOne_projects (g : TaggedGro) (e : GroEntry) (segs : Nat) :
    ProjectsPrefix removedId? TaggedGro.erase (groNormalOneTagged g e segs)
      (groNormalOnePrefix (fun bytes => liftPrefix (bytes.forM Leanux.Env.deliverInner))
        g.erase e.bytes segs) := by
  unfold groNormalOneTagged groNormalOnePrefix
  dsimp only [TaggedGro.erase]
  split
  · simpa [TaggedGro.erase, List.map_append] using
      groNormalList_projects {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  · simpa [TaggedGro.erase, List.map_append] using
      projectsPrefix_pure removedId? TaggedGro.erase
        {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}

theorem napiGroReceive_projects (g : TaggedGro) (e : GroEntry) :
    ProjectsPrefix removedId? TaggedGro.erase (napiGroReceiveTagged g e)
      (napiGroReceivePrefix (fun bytes => liftPrefix (bytes.forM Leanux.Env.deliverInner))
        g.erase e.bytes) := by
  have pure_eq (g : TaggedGro) (a : GroState) (he : g.erase = a) :
      ProjectsPrefix removedId? TaggedGro.erase (pure g : PrefixM GroEvent TaggedGro) (pure a) := by
    rw [← he]
    exact projectsPrefix_pure _ _ _
  rcases g with ⟨xs, count, held⟩
  cases held <;> try (rename_i old rest; cases rest)
  all_goals
    unfold napiGroReceiveTagged napiGroReceivePrefix
    simp only [TaggedGro.erase, List.map_cons, List.map_nil]
    repeat' first
      | contradiction
      | with_reducible exact groNormalOne_projects _ _ _
      | with_reducible exact projectsPrefix_pure _ _ _
      | with_reducible exact projectsPrefix_lift _ _
      | with_reducible apply projectsPrefix_ite
      | with_reducible apply projectsPrefix_bind removedId? TaggedGro.erase TaggedGro.erase
      | with_reducible apply projectsPrefix_bind removedId? id TaggedGro.erase
      | (with_reducible intro x; try dsimp only)
      | (split <;> simp_all only)
    all_goals first
      | exact groNormalOne_projects _ _ _
      | (apply pure_eq; simp only [TaggedGro.erase, List.map_append, List.map_cons, List.map_nil])
      | exact fun _ _ => rfl

theorem napiGroFlushAll_projects (gro : TaggedGro) :
    ProjectsPrefix removedId? id (napiGroFlushAllTagged gro)
      (napiGroFlushAllPrefix (fun bytes => liftPrefix (bytes.forM Leanux.Env.deliverInner)) gro.erase) := by
  unfold napiGroFlushAllTagged napiGroFlushAllPrefix
  apply projectsPrefix_bind removedId? TaggedGro.erase id
  · apply projectsPrefix_forIn_map removedId? TaggedGro.erase GroEntry.bytes
    intro e g
    exact projectsPrefix_bind removedId? TaggedGro.erase (projectStep TaggedGro.erase)
      (groNormalOne_projects g e 1)
      (fun g => projectsPrefix_pure removedId? (projectStep TaggedGro.erase) (.yield g))
  · intro g
    apply projectsPrefix_bind removedId? TaggedGro.erase id (groNormalList_projects {g with held := []})
    intro _
    exact projectsPrefix_pure removedId? id ()

theorem groOption_projects (g : TaggedGro) (out : Option GroEntry) :
    ProjectsPrefix removedId? TaggedGro.erase (out.elim (pure g) (napiGroReceiveTagged g))
      ((out.toList.map GroEntry.bytes).foldlM
        (fun g bytes => napiGroReceivePrefix
          (fun bs => liftPrefix (bs.forM Leanux.Env.deliverInner)) g bytes) g.erase) := by
  cases out with
  | none => exact projectsPrefix_pure removedId? TaggedGro.erase g
  | some e => simpa using napiGroReceive_projects g e

/-- Projection compares complete runs of the two existing observers, rather
than deriving log agreement from their separate original-result erasures. -/
theorem rxPollGro_projects (pid : PeerId) (budget : Nat) :
    ProjectsPrefix removedId? id (rxPollGro pid budget)
      (rxPollRemovals pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  unfold rxPollGro rxPollRemovals
  apply projectsPrefix_bind removedId? id id (projectsPrefix_lift _ _)
  intro noBudget
  dsimp only [id]
  apply projectsPrefix_ite
  · intro hb
    exact projectsPrefix_pure removedId? id _
  · intro hb
    apply projectsPrefix_bind removedId? pollProject id
    · apply projectsPrefix_range removedId? pollProject
      intro n acc
      repeat' first
        | with_reducible exact projectsPrefix_lift removedId? _
        | with_reducible exact dropGro_projects _ _ _
        | with_reducible exact consumeGro_projects _ _ _ _ _
        | with_reducible exact napiGroReceive_projects _ _
        | with_reducible exact groOption_projects _ _
        | with_reducible apply projectsPrefix_forIn_map removedId? TaggedGro.erase GroEntry.bytes
        | with_reducible apply projectsPrefix_bind removedId? TaggedGro.erase
        | with_reducible apply projectsPrefix_bind removedId? (Option.map GroEntry.bytes)
        | with_reducible apply projectsPrefix_bind removedId? id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id, pollProject]; try simp only [Option.toList_map])
        | (with_reducible split)
        | (simpa [pollProject, projectStep, List.map_append, Option.toList_map] using
            projectsPrefix_pure removedId? (projectStep pollProject) _)
        | with_reducible exact projectsPrefix_pure removedId? (projectStep TaggedGro.erase) _
      all_goals simp_all [ProjectsPrefix, Option.toList_map, Except.map]
      all_goals first
        | exact groOption_projects _ _
        | (intro w; split <;> simp_all only)
    · intro acc
      dsimp only [pollProject]
      repeat' first
        | with_reducible exact projectsPrefix_lift removedId? _
        | with_reducible exact napiGroFlushAll_projects _
        | with_reducible exact projectsPrefix_pure removedId? id _
        | with_reducible apply projectsPrefix_bind removedId? id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id])
        | (with_reducible split)
      all_goals simp_all [ProjectsPrefix, Except.map]

theorem rxPollGro_removals_agree (pid : PeerId) (budget : Nat) (w : World) :
    runPrefix (rxPollRemovals pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) w [] =
      ((runPrefix (rxPollGro pid budget) w []).1,
       (removedTags (runPrefix (rxPollGro pid budget) w []).2).map Prod.snd) := by
  have he := rxPollGro_projects pid budget w []
  simp only [List.filterMap_nil] at he
  rw [removedId_eq] at he
  have hm : (runPrefix (rxPollGro pid budget) w []).1.map
      (fun (x, v) => (id x, v)) = (runPrefix (rxPollGro pid budget) w []).1 := by
    cases (runPrefix (rxPollGro pid budget) w []).1 <;> rfl
  rw [hm] at he
  exact he

end Leanux.Proofs.WG.Queues
