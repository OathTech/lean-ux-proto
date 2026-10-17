import Leanux.Proofs.WG.Queues.RxPollHistory

/-! The existing observed poll starts a fresh local journal from the incoming
lifetime history and promotes only its newly appended suffix. The source below
makes that boundary available to product callbacks with additional events;
it does not run a trial or rebuild any scheduler marker. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.ObserveSource
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The literal seed/run/suffix boundary of the existing observed poll. -/
def seededWith {E L α : Type} (seed : List E → List L) (promote : L → E)
    (poll : PrefixM L α) : PrefixM E α :=
  fun w => ExceptT.mk fun h =>
    let initial := seed h
    let out := runPrefix poll w initial
    (out.1, h ++ (out.2.drop initial.length).map promote)

theorem seeded_suffix {E L α : Type} (seed : List E → List L) (promote : L → E)
    (poll : PrefixM L α) (w : World) (h : List E)
    (out : Except Stop (α × World)) (suffix : List L)
    (he : runPrefix poll w (seed h) = (out, seed h ++ suffix)) :
    runPrefix (seededWith seed promote poll) w h = (out, h ++ suffix.map promote) := by
  change ((runPrefix poll w _).1, h ++ ((runPrefix poll w _).2.drop _).map _) = _
  rw [he]
  simp only [List.drop_append_length]

theorem seeded_appends {E L α : Type} (seed : List E → List L) (promote : L → E)
    (poll : PrefixM L α) : Appends (seededWith seed promote poll) :=
  fun _ _ => ⟨_, rfl⟩

theorem seeded_erases {E L α : Type} (seed : List E → List L) (promote : L → E)
    (poll : PrefixM L α) (original : Leanux.M α) (he : ErasesPrefix poll original) :
    ErasesPrefix (seededWith seed promote poll) original := fun w h => he w (seed h)

/-- Exact projection needs the callback's actual appended seed. No length
argument is inferred from event equality or occurrence uniqueness. -/
theorem seeded_projects {E F L K α β : Type}
    (global : E → Option F) (localEvent : L → Option K) (result : α → β)
    (seed : List E → List L) (lowerSeed : List F → List K)
    (promote : L → E) (lowerPromote : K → F)
    (poll : PrefixM L α) (lower : PrefixM K β)
    (seeds : ∀ h, (seed h).filterMap localEvent = lowerSeed (h.filterMap global))
    (promotions : ∀ e, global (promote e) = (localEvent e).map lowerPromote)
    (append : Appends poll) (projects : ProjectsPrefix localEvent result poll lower) :
    ProjectsPrefix global result (seededWith seed promote poll)
      (seededWith lowerSeed lowerPromote lower) := by
  intro w h
  obtain ⟨suffix, hs⟩ := append w (seed h)
  have high := seeded_suffix seed promote poll w h _ suffix (Prod.ext rfl hs)
  have lowRun := projects w (seed h)
  rw [seeds h, hs, List.filterMap_append, seeds h] at lowRun
  have low := seeded_suffix lowerSeed lowerPromote lower w (h.filterMap global)
    _ (suffix.filterMap localEvent) lowRun
  have mapped : (suffix.map promote).filterMap global =
      (suffix.filterMap localEvent).map lowerPromote := by
    clear hs high lowRun low
    induction suffix with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, List.filterMap_cons, promotions]
      cases localEvent e <;> simp only [Option.map_none, Option.map_some,
        List.map_cons, ih]
  rw [high, low, List.filterMap_append, mapped]

/-- The previous observer is the identical source boundary, not a second run. -/
theorem observePoll_factor (pid : PeerId) (budget : Nat) :
    observePoll pid budget =
      seededWith (fun h => RxJoint.seed (prior h)) promote (RxJoint.poll pid budget) := rfl

/-- An extended poll still receives only the fresh seed of the previous
lifetime history. Older probes and new-kind global events stay in the global
prefix and are not replayed as local poll events. -/
def observePollWith {E L : Type} (oldEvent : E → Option Event)
    (encode : RxJoint.Event → L) (promote : L → E) (poll : PrefixM L Nat) : PrefixM E Nat :=
  seededWith (fun h => (RxJoint.seed (prior (h.filterMap oldEvent))).map encode) promote poll

theorem observePollWith_projects {E L : Type} (oldEvent : E → Option Event)
    (localEvent : L → Option RxJoint.Event) (encode : RxJoint.Event → L)
    (promote : L → E) (poll : PrefixM L Nat) (pid : PeerId) (budget : Nat)
    (inverse : ∀ e, localEvent (encode e) = some e)
    (promotions : ∀ e, oldEvent (promote e) = (localEvent e).map RxHistory.promote)
    (append : Appends poll) (projects : ProjectsPrefix localEvent id poll (RxJoint.poll pid budget)) :
    ProjectsPrefix oldEvent id (observePollWith oldEvent encode promote poll) (observePoll pid budget) := by
  rw [observePoll_factor]
  exact seeded_projects oldEvent localEvent id _ _ _ _ _ _
    (fun h => filterMap_encoded encode localEvent inverse _)
    promotions append projects

theorem observePollWith_appends {E L : Type} (oldEvent : E → Option Event)
    (encode : RxJoint.Event → L) (promote : L → E) (poll : PrefixM L Nat) :
    Appends (observePollWith oldEvent encode promote poll) := seeded_appends _ _ _

theorem observePollWith_erases {E L : Type} (oldEvent : E → Option Event)
    (encode : RxJoint.Event → L) (promote : L → E) (poll : PrefixM L Nat)
    (original : Leanux.M Nat) (he : ErasesPrefix poll original) :
    ErasesPrefix (observePollWith oldEvent encode promote poll) original := seeded_erases _ _ _ _ he

end Leanux.Proofs.WG.Queues.RxHistory.ObserveSource
