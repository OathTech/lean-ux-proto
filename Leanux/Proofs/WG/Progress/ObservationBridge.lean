import Leanux.Proofs.WG.Progress.View
import Leanux.Proofs.WG.Progress.SchedulerSourceClaims
import Leanux.Proofs.WG.Progress.ControlSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Concrete execution adapters for projected observations. Inspection runs on
a copy of the actual entry state. Every prefix, hidden read, activation and
post-poll peek keeps its actual concrete intermediate state. -/
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Campaign2.Product

def probeObservation (a : Activation) : M ProbeObservation := fun w =>
  .ok (⟨observeResult ((Activation.consistent a).run w),
    observeResult ((Activation.run a).run w)⟩, w)

/-- Decorate the original sequential dispatch factor with its actual selection
and section-start observations. This does not stitch independent runs. -/
def tracedDispatch (worker : Worker) : M (Option DispatchTrace) := fun initial =>
  (dispatchPrefix worker).run initial >>= fun (choice, selected) =>
    match choice with
    | none => .ok (none, selected)
    | some pid => (hidden (.sectionStart worker) : Leanux.M (List UInt8)).run selected >>= fun (bytes, started) =>
      (Activation.run { worker, pid }).run started >>= fun (_, final) =>
        .ok (some ⟨pid, snapshot selected, bytes, snapshot started⟩, final)

theorem tracedDispatch_erase (worker : Worker) :
    Env.dispatch worker = (do let trace ← tracedDispatch worker; pure trace.isSome) := by
  have hok {α β : Type} (x : α) (f : α → Except Stop β) : (Except.ok x >>= f) = f x := rfl
  funext w
  change (Env.dispatch worker).run w =
    (do let trace ← tracedDispatch worker; pure trace.isSome : M Bool).run w
  rw [dispatch_source]
  simp only [StateT.run_bind]
  change ((dispatchPrefix worker).run w >>= fun out => (dispatchAfterPrefix worker out.1).run out.2) =
    (((dispatchPrefix worker).run w >>= fun (choice, selected) =>
      match choice with
      | none => .ok (none, selected)
      | some pid => (hidden (.sectionStart worker) : Leanux.M (List UInt8)).run selected >>= fun (bytes, started) =>
        (Activation.run { worker, pid }).run started >>= fun (_, final) =>
          .ok (some (DispatchTrace.mk pid (snapshot selected) bytes (snapshot started)), final)) >>=
        fun (trace, final) => .ok (trace.isSome, final))
  cases hp : (dispatchPrefix worker).run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨choice, selected⟩ := pair
    cases choice with
    | none => rfl
    | some pid =>
      simp only [hok]
      change ((hidden (.sectionStart worker) : Leanux.M (List UInt8)).run selected >>= fun out =>
        ((Activation.run { worker, pid }).run out.2 >>= fun after => Except.ok (true, after.2))) = _
      cases hs : (hidden (.sectionStart worker) : Leanux.M (List UInt8)).run selected with
      | error e => rfl
      | ok pair =>
        obtain ⟨bytes, started⟩ := pair
        simp only [hok]
        cases ha : (Activation.run { worker, pid }).run started with
        | error e => rfl
        | ok pair => obtain ⟨u, final⟩ := pair; cases u; rfl

def observeDispatch (worker : Worker) (w : World) : DispatchObservation :=
  ⟨observeResult ((Env.dispatch worker).run w), observeResult ((dispatchPrefix worker).run w),
    observeResult ((tracedDispatch worker).run w)⟩

def dispatchObservation (worker : Worker) : M DispatchObservation := fun w =>
  .ok (observeDispatch worker w, w)

def candidateObservation (candidates : List Activation) : M CandidateObservation := fun w =>
  .ok (⟨observeResult ((candidates.filterM Activation.consistent).run w),
    fun a => observeResult ((Activation.run a).run w)⟩, w)

def tracedNapi : M (Snapshot × Option Nat) := fun initial =>
  napiSoftirq.run initial >>= fun (_, afterPoll) =>
    (peekHiddenSite : Leanux.M (Option Nat)).run afterPoll >>= fun (next, final) =>
      .ok ((snapshot afterPoll, next), final)

theorem tracedNapi_erase : napiTurn = (do let observation ← tracedNapi; pure (napiResult observation)) := by
  have hok {α β : Type} (x : α) (f : α → Except Stop β) : (Except.ok x >>= f) = f x := rfl
  funext w
  change napiTurn.run w = (do let observation ← tracedNapi; pure (napiResult observation) : M TurnResult).run w
  simp only [napiTurn, StateT.run_bind]
  change (napiSoftirq.run w >>= fun out =>
    ((peekHiddenSite : Leanux.M (Option Nat)).run out.2 >>= fun after =>
      (if after.1 == some (HiddenSite.sectionStart .netRx).info.id then pure turnReturn
        else pure turnContinue : M TurnResult).run after.2)) =
    ((napiSoftirq.run w >>= fun (_, afterPoll) =>
      (peekHiddenSite : Leanux.M (Option Nat)).run afterPoll >>= fun (next, final) =>
        Except.ok ((snapshot afterPoll, next), final)) >>= fun (value, final) =>
          Except.ok (napiResult value, final))
  cases hp : napiSoftirq.run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, afterPoll⟩ := pair
    simp only [hok]
    cases hn : (peekHiddenSite : Leanux.M (Option Nat)).run afterPoll with
    | error e => rfl
    | ok pair =>
      obtain ⟨next, final⟩ := pair
      simp only [hok]
      unfold napiResult
      split <;> rfl

def observeAfterPeek (next : Option Nat) (w : World) : TurnAfterPeek where
  state := snapshot w
  next := next
  candidates := observeResult ((w.ambient.suspended.filterM Activation.consistent).run w)
  guard := fun worker => observeResult ((Activation.hasWork { worker }).run w)
  resumed := fun a => observeResult ((resumeCandidates none [a]).run w)
  dispatch := fun worker => observeDispatch worker w
  napi := observeResult (tracedNapi.run w)

def turnObservation (stack : Option Worker) : M TurnObservation := fun w =>
  .ok (⟨observeResult ((scheduleTurn stack).run w),
    ((peekHiddenSite : Leanux.M (Option Nat)).run w).map fun (next, after) => observeAfterPeek next after⟩, w)

def recordlessObservation (stack : Option Worker) (worker : Worker) :
    M (Outcome TurnResult × DispatchObservation) := fun w =>
  .ok ((observeResult ((scheduleTurn stack).run w), observeDispatch worker w), w)

theorem turn_contract (stack : Option Worker) (P : Snapshot → Prop)
    (Q : Outcome TurnResult → TurnAfterPeek → Prop)
    (h : ∀ initial next after, P (snapshot initial) →
      (peekHiddenSite : Leanux.M (Option Nat)).run initial = .ok (next, after) →
      Q (observeResult ((scheduleTurn stack).run initial)) (observeAfterPeek next after)) :
    Returns (turnObservation stack) P
      (fun observation _ => ∀ after, observation.afterPeek = .ok after → Q observation.actual after) := by
  intro w pre
  refine ⟨_, w, rfl, ?_⟩
  intro observed same
  change ((peekHiddenSite : Leanux.M (Option Nat)).run w).map _ = .ok observed at same
  cases hp : (peekHiddenSite : Leanux.M (Option Nat)).run w with
  | error err => rw [hp] at same; cases same
  | ok pair =>
    obtain ⟨next, v⟩ := pair
    rw [hp] at same
    have eq := Except.ok.inj same
    subst observed
    exact h w next v pre hp

theorem observe_map (f : α → β) (out : Except Stop (α × World)) :
    observeResult (out >>= fun (value, final) => .ok (f value, final)) =
      mapOutcome f (observeResult out) := by
  cases out <;> rfl

theorem observe_success_iff {α β : Type}
    (left : Except Stop (α × World)) (right : Except Stop (β × World))
    (x : α) (y : β) (s : Snapshot)
    (h : ∀ w, left = .ok (x, w) ↔ right = .ok (y, w)) :
    observeResult left = .ok (x, s) ↔ observeResult right = .ok (y, s) := by
  constructor
  · intro hl
    cases left with
    | error e => cases hl
    | ok pair =>
      obtain ⟨value, w⟩ := pair
      change Except.ok (value, snapshot w) = Except.ok (x, s) at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hl)
      rw [(h w).mp rfl]
      rfl
  · intro hr
    cases right with
    | error e => cases hr
    | ok pair =>
      obtain ⟨value, w⟩ := pair
      change Except.ok (value, snapshot w) = Except.ok (y, s) at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hr)
      rw [(h w).mpr rfl]
      rfl

theorem observe_error_iff (out : Except Stop (α × World)) (err : Stop) :
    observeResult out = .error err ↔ out = .error err := by
  cases out <;> simp [observeResult, Except.map]

theorem filter_observation {xs : List Activation} {w : World} {result : List Activation}
    (h : observeResult ((xs.filterM Activation.consistent).run w) = .ok (result, snapshot w)) :
    (xs.filterM Activation.consistent).run w = .ok (result, w) := by
  cases hr : (xs.filterM Activation.consistent).run w with
  | error e => rw [hr] at h; cases h
  | ok pair =>
    obtain ⟨value, v⟩ := pair
    obtain ⟨same, _⟩ := filter_consistent_result xs w v value hr
    subst v
    rw [hr] at h
    change Except.ok (value, snapshot w) = Except.ok (result, snapshot w) at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    rfl

theorem guard_observation {a : Activation} {w : World} {result : Bool}
    (h : observeResult ((Activation.hasWork a).run w) = .ok (result, snapshot w)) :
    (Activation.hasWork a).run w = .ok (result, w) := by
  cases hr : (Activation.hasWork a).run w with
  | error e => rw [hr] at h; cases h
  | ok pair =>
    obtain ⟨value, v⟩ := pair
    have same := hasWork_world a w w value v rfl hr
    subst v
    rw [hr] at h
    change Except.ok (value, snapshot w) = Except.ok (result, snapshot w) at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    rfl

theorem dispatch_observation_exact (worker : Worker) (w : World) :
    (observeDispatch worker w).actual = mapOutcome Option.isSome (observeDispatch worker w).traced := by
  change observeResult ((Env.dispatch worker).run w) = _
  rw [tracedDispatch_erase, StateT.run_bind]
  exact observe_map Option.isSome ((tracedDispatch worker).run w)

theorem traced_success_iff (worker : Worker) (w : World) (s : Snapshot) :
    (observeDispatch worker w).actual = .ok (true, s) ↔
      ∃ trace, (observeDispatch worker w).traced = .ok (some trace, s) := by
  rw [dispatch_observation_exact]
  cases h : (observeDispatch worker w).traced with
  | error e => simp [mapOutcome, Except.map]
  | ok pair =>
    obtain ⟨choice, final⟩ := pair
    cases choice <;> simp [mapOutcome, Except.map, eq_comm]

end Leanux.Proofs.WG.Progress
