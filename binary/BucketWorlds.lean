import BucketScan

namespace Binary.LookupSearch
open Leanux Leanux.WG

def recordStep (world : World) (step : Step) : World :=
  {world with steps := world.steps.push step}

def advance : World → List Step → World
  | world, [] => world
  | world, step :: rest => advance (recordStep world step) rest

/-- Source Worlds immediately after each decision, including the two
    decisions that a terminal binary guard may emit on one machine edge. -/
def decisionWorlds : World → List Step → List MirrorHistory.Point
  | _, [] => []
  | world, step :: rest =>
      let next := recordStep world step
      ⟨.decision step.decision, next⟩ :: decisionWorlds next rest

theorem advance_eq (world : World) (steps : List Step) :
    advance world steps = {world with steps := world.steps ++ steps.toArray} := by
  induction steps generalizing world with
  | nil => simp [advance]
  | cons step rest ih =>
    rw [advance, ih]
    simp [recordStep]

theorem advance_append (world : World) (first second : List Step) :
    advance world (first ++ second) = advance (advance world first) second := by
  induction first generalizing world with
  | nil => rfl
  | cons step rest ih => exact ih (recordStep world step)

theorem decisionWorlds_append (world : World) (first second : List Step) :
    decisionWorlds world (first ++ second) =
      decisionWorlds world first ++ decisionWorlds (advance world first) second := by
  induction first generalizing world with
  | nil => rfl
  | cons step rest ih => simp only [List.cons_append, decisionWorlds, ih, advance]

/-- Exact log and final World of the operational source bucket prefix.
    This strengthens result_world/source_bucket_steps: no intermediate
    World is selected independently of the accepted source execution. -/
theorem result_worlds (kinds : List IndexKind) (query : Nat)
    (es : List (Address × IndexEntry)) (history : List MirrorHistory.Point) (world : World) :
    (result kinds query (es.map Prod.snd) history world).1.2 =
      history ++ decisionWorlds world (LookupHistory.bucketSteps world.netRxSection query kinds es) ∧
    (result kinds query (es.map Prod.snd) history world).2 =
      advance world (LookupHistory.bucketSteps world.netRxSection query kinds es) := by
  induction es generalizing history world with
  | nil =>
    simp [result_nil, finish, decisionWorlds, advance, LookupHistory.bucketSteps,
      recordStep, LookupMirror.record]
  | cons cell rest ih =>
    rcases cell with ⟨address, entry⟩
    cases hit : (entry.index == query) with
    | false =>
      rw [List.map_cons, result_miss kinds query entry _ history world hit]
      have recursive := ih
        (history ++ [⟨.decision .idxWalk, LookupMirror.record world .idxWalk true⟩] ++
          [⟨.decision .idxMatch, LookupMirror.record (LookupMirror.record world .idxWalk true) .idxMatch false⟩])
        (LookupMirror.record (LookupMirror.record world .idxWalk true) .idxMatch false)
      simpa only [LookupHistory.bucketSteps, hit, Bool.false_eq_true, ite_false,
        decisionWorlds, advance, LookupMirror.record, recordStep, List.cons_append,
        List.nil_append, List.append_assoc] using recursive
    | true =>
      rw [List.map_cons, result_hit kinds query entry _ history world hit]
      cases good : kinds.contains entry.kind <;>
        simp [finish, LookupHistory.bucketSteps, hit, good, decisionWorlds, advance,
          recordStep, LookupMirror.record, List.append_assoc]

/-- Each source checkpoint has precisely the cumulative step prefix and
    all other World fields unchanged. The unrelated fields need not be
    constrained by the machine relation to prove this source equation. -/
theorem decisionWorlds_get (world : World) (steps : List Step) (i : Nat)
    (point : MirrorHistory.Point) (present : (decisionWorlds world steps)[i]? = some point) :
    ∃ step, steps[i]? = some step ∧ point.tag = .decision step.decision ∧
      point.world = {world with steps := world.steps ++ (steps.take (i + 1)).toArray} ∧
      point.world.steps.back? = some step := by
  induction steps generalizing world i with
  | nil => simp [decisionWorlds] at present
  | cons step rest ih =>
    cases i with
    | zero =>
      have equal : point = ⟨.decision step.decision, recordStep world step⟩ := by
        simpa only [decisionWorlds, List.getElem?_cons_zero, Option.some.injEq] using present.symm
      subst point
      refine ⟨step, rfl, rfl, ?_, ?_⟩
      · simp [recordStep]
      · simp [recordStep]
    | succ i =>
      have tail : (decisionWorlds (recordStep world step) rest)[i]? = some point := present
      obtain ⟨last, found, tag, eq, back⟩ := ih (recordStep world step) i tail
      refine ⟨last, found, tag, ?_, back⟩
      simpa [recordStep] using eq

/-- The very first index match determines the source suffix, including
    a rejected kind. No distinct-index invariant or second search is used. -/
theorem result_answer (kinds : List IndexKind) (query : Nat)
    (es : List (Address × IndexEntry)) (history : List MirrorHistory.Point) (world : World) :
    (result kinds query (es.map Prod.snd) history world).1.1 =
      (LookupHistory.firstIndex query es).bind
        (fun cell => if kinds.contains cell.2.kind then some cell.2 else none) := by
  induction es generalizing history world with
  | nil => rfl
  | cons cell rest ih =>
    rcases cell with ⟨address, entry⟩
    cases hit : (entry.index == query) with
    | false =>
      rw [List.map_cons, result_miss kinds query entry _ history world hit]
      simpa only [LookupHistory.firstIndex, hit, Bool.false_eq_true, ite_false] using ih _ _
    | true =>
      rw [List.map_cons, result_hit kinds query entry _ history world hit]
      cases good : kinds.contains entry.kind <;>
        simp [LookupHistory.firstIndex, hit, good, finish]

theorem decisionWorlds_take (world : World) (steps : List Step) (n : Nat) :
    (decisionWorlds world steps).take n = decisionWorlds world (steps.take n) := by
  induction steps generalizing world n with
  | nil => simp [decisionWorlds]
  | cons step rest ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [decisionWorlds, List.take_succ_cons, ih]

/-- The latest source World at a stuttering machine cut, including zero
    appended decisions. It is fixed by the preceding source checkpoint. -/
theorem latest_world (history : List MirrorHistory.Point) (world : World)
    (latest : history.getLast?.map (·.world) = some world) (steps : List Step) :
    (history ++ decisionWorlds world steps).getLast?.map (·.world) =
      some (advance world steps) := by
  induction steps generalizing history world with
  | nil => simpa only [decisionWorlds, List.append_nil, advance] using latest
  | cons step rest ih =>
    have next := ih (history ++ [⟨.decision step.decision, recordStep world step⟩])
      (recordStep world step) (by simp)
    simpa only [List.append_assoc, List.singleton_append, decisionWorlds, advance] using next

theorem latest_world_take (history : List MirrorHistory.Point) (world : World)
    (latest : history.getLast?.map (·.world) = some world) (steps : List Step) (n : Nat) :
    (history ++ (decisionWorlds world steps).take n).getLast?.map (·.world) =
      some (advance world (steps.take n)) := by
  rw [decisionWorlds_take]
  exact latest_world history world latest _

/-- Actual decision records determine every source checkpoint, including
    its tag and final log entry. The remaining obligation is the physical
    relation at that checkpoint; no expected trace is supplied here. -/
theorem match_decisions (R : LookupObservation.Relation)
    (seen delta : List LookupObservation.Point) (world : World)
    (tags : LookupHistory.DecisionPoints delta)
    (related : ∀ before point after, delta = before ++ point :: after →
      R (seen ++ before ++ [point]) point.machine
        (advance world ((before ++ [point]).filterMap (·.step)))) :
    LookupObservation.MatchesPointsFrom R seen delta
      (decisionWorlds world (delta.filterMap (·.step))) := by
  induction delta generalizing seen world with
  | nil => exact .nil
  | cons point rest ih =>
    obtain ⟨step, record, tag⟩ := tags point (by simp)
    simp only [List.filterMap_cons, record, decisionWorlds]
    apply LookupObservation.MatchesPointsFrom.cons
    · refine ⟨tag, ?_, ?_⟩
      · have h := related [] point rest rfl
        simpa only [List.append_nil, List.nil_append, List.filterMap_cons,
          List.filterMap_nil, record, advance] using h
      · simp [record, recordStep]
    · apply ih (seen ++ [point]) (recordStep world step)
      · intro q member
        exact tags q (by simp [member])
      · intro before q after decomposition
        have h := related (point :: before) q after (by simp [decomposition])
        simpa only [List.cons_append, List.filterMap_cons, record, advance,
          List.append_assoc, List.singleton_append, List.nil_append] using h

#print axioms match_decisions
#print axioms latest_world_take
#print axioms latest_world
#print axioms decisionWorlds_take
#print axioms advance_eq
#print axioms advance_append
#print axioms decisionWorlds_append
#print axioms result_worlds
#print axioms decisionWorlds_get
#print axioms result_answer
end Binary.LookupSearch

namespace Binary.LookupHistory
open TrustBase

theorem bucketExitBase_memory (base : MachineData) (query : Nat)
    (es : List (Address × Leanux.WG.IndexEntry)) :
    (bucketExitBase base query es).dmem = base.dmem := by
  simp only [bucketExitBase]
  split <;> rfl

theorem bucketExitBase_writes (base : MachineData) (coverage : LookupCoverage.Context) (query : Nat)
    (es : List (Address × Leanux.WG.IndexEntry)) :
    scanWrites (bucketExitBase base query es) coverage = scanWrites base coverage := by
  simp only [bucketExitBase]
  split <;> rfl

/-- R's stable WG footprint sees one memory frame across both loop phases.
    The post-AND register mask really changes, so this intentionally does
    not claim ScanFrame base after the AND. -/
theorem bucketCuts_memory (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (query : Nat) (es : List (Address × Leanux.WG.IndexEntry))
    (before after : List MachineState)
    (first : ScanCuts base coverage preempt before)
    (second : ScanCuts (bucketExitBase base query es) coverage preempt after) :
    ∀ state ∈ before ++ after, state.pc ∈ Image.cutPoints →
      EqualOutside (scanWrites base coverage) base.dmem state.data.dmem := by
  intro state member cut
  rcases List.mem_append.mp member with front | back
  · exact (first state front cut).memory
  · simpa only [bucketExitBase_writes, bucketExitBase_memory] using (second state back cut).memory

#print axioms bucketExitBase_memory
#print axioms bucketExitBase_writes
#print axioms bucketCuts_memory
end Binary.LookupHistory
