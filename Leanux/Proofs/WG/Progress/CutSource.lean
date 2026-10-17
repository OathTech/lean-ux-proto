import Leanux.Proofs.WG.Progress.CutFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux

abbrev CutState := Option (List Nat) × List Nat

/-- One unchanged original cut iteration, including its explicit return. -/
def cutStep (sites : List HiddenSite) (_ : Nat) (state : CutState) : AmbientM (ForInStep CutState) := do
  AmbientM.skipAmbient
  let w ← get
  match w.hidden with
  | some (r :: rest) =>
    if !(cutIds sites).contains r.site then return .done (some state.2, state.2)
    if let some i := (AllocSite.cuts.map fun s => (HiddenSite.alloc s).info).find? (·.id == r.site) then
      if r.bytes.headD 1 != 1 then
        AmbientM.unsupported s!"a below-cut allocation failed ({i.label}, {i.file}:{i.line})"
    set { w with hidden := some rest }
    AmbientM.noteNetRxStart r.site
    return .yield (none, state.2 ++ [r.site])
  | _ => return .done (some state.2, state.2)

def cutFinish (state : CutState) : AmbientM (List Nat) := do
  match state.1 with
  | some taken => pure taken
  | none => AmbientM.budgetExhausted "a cut point's records"

theorem skipCutSites_source (sites : List HiddenSite) :
    AmbientM.skipCutSites sites = (do
      let budget ← AmbientM.recordBudget
      let state ← forIn ([:budget] : Std.Legacy.Range) (none, []) (cutStep sites)
      cutFinish state) := by
  simp only [AmbientM.skipCutSites, cutFinish]
  congr 1
  funext budget
  congr 1
  funext state
  cases state.1 <;> rfl

/-- Ambient consumption is an exact source effect, not an untouched-field frame. -/
theorem skipAmbient_run (w : Ambient) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    AmbientM.skipAmbient.run w = .ok ((), { w with hidden := some (records.dropWhile fun r => HiddenSite.passive r.site) }) := by
  simp [AmbientM.skipAmbient, present, StateT.run, Bind.bind, bind, pure, get, getThe, MonadStateOf.get,
    set, StateT.bind, StateT.get, StateT.set, Except.pure, Except.bind]

def cutAdvanced (w : Ambient) (rest : List HiddenRecord) (site : Nat) : Ambient :=
  let after := { w with hidden := some rest }
  if site == (HiddenSite.sectionStart .netRx).info.id then
    { after with netRxSections := after.netRxSections + 1 }
  else after

/-- A recorded step either stops, propagates the original allocation failure,
or removes the selected head after discarding ambient records. -/
theorem cutStep_recorded (sites : List HiddenSite) (turn : Nat) (state : CutState)
    (w : Ambient) (records : List HiddenRecord) (present : w.hidden = some records) :
    (cutStep sites turn state).run w =
      match records.dropWhile (fun r => HiddenSite.passive r.site) with
      | [] => .ok (.done (some state.2, state.2), { w with hidden := some [] })
      | record :: rest =>
        if !(cutIds sites).contains record.site then
          .ok (.done (some state.2, state.2), { w with hidden := some (record :: rest) })
        else match cutFailure record with
        | some message => .error (.outsideDomain (cutErrorLocation w.steps) message)
        | none => .ok (.yield (none, state.2 ++ [record.site]), cutAdvanced w rest record.site) := by
  simp only [cutStep, StateT.run_bind, skipAmbient_run w records present]
  cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil => rfl
  | cons record rest =>
    dsimp only [Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
      StateT.get, Pure.pure, Except.bind, Except.pure]
    by_cases selected : (cutIds sites).contains record.site = true
    · simp only [selected, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases allocation : (AllocSite.cuts.map fun s => (HiddenSite.alloc s).info).find? (·.id == record.site) with
      | none =>
        simp only [cutFailure, allocation]
        unfold cutAdvanced AmbientM.noteNetRxStart
        split <;> rfl
      | some info =>
        by_cases accepted : record.bytes.headD 1 = 1
        · simp only [cutFailure, allocation, accepted, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          unfold cutAdvanced AmbientM.noteNetRxStart
          split <;> rfl
        · have rejected : (record.bytes.headD 1 != 1) = true := by simpa only [bne_iff_ne] using accepted
          simp only [cutFailure, allocation, rejected, ↓reduceIte]
          rfl
    · have rejected : (cutIds sites).contains record.site = false := by simpa using selected
      simp only [rejected, Bool.not_false, ↓reduceIte]
      rfl

def cutLoop (sites : List HiddenSite) (turns : List Nat) (taken : List Nat) : AmbientM CutState :=
  forIn turns (none, taken) (cutStep sites)

/-- The loop always reaches an original return or the original allocation
failure before its fuel ends. The accepted-prefix hypothesis is not needed
for this outcome classification. -/
theorem cutLoop_outcome (sites : List HiddenSite) (turns : List Nat)
    (w : Ambient) (records : List HiddenRecord) (taken : List Nat)
    (present : w.hidden = some records) (enough : records.length + 1 ≤ turns.length) :
    (∃ extra rest final,
      (cutLoop sites turns taken).run w = .ok ((some (taken ++ extra), taken ++ extra), final) ∧
      final.hidden = some rest ∧ final.steps = w.steps ∧ CutProgress sites records extra rest) ∨
    (∃ message, (cutLoop sites turns taken).run w =
      .error (.outsideDomain (cutErrorLocation w.steps) message) ∧
      CutFailure sites records message ∧ ¬ CutAccepted sites records) := by
  induction turns generalizing w records taken with
  | nil => simp at enough
  | cons turn turns ih =>
    have suffix := List.dropWhile_suffix (l := records) (fun r => HiddenSite.passive r.site)
    have first := cutStep_recorded sites turn (none, taken) w records present
    cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
    | nil =>
      simp only [stripped] at first
      left
      refine ⟨[], [], { w with hidden := some [] }, ?_, rfl, rfl, ?_⟩
      · simp only [cutLoop, List.forIn_cons, StateT.run_bind, first, List.append_nil]
        rfl
      · exact ⟨List.nil_suffix, by simp, by simp, trivial⟩
    | cons record rest =>
      rw [stripped] at suffix
      have passive : HiddenSite.passive record.site = false := by
        have h := List.head?_dropWhile_not (fun r => HiddenSite.passive r.site) records
        simpa [stripped] using h
      have suffixRest : rest.IsSuffix records := (List.suffix_cons record rest).trans suffix
      have shorter : rest.length < records.length := by
        have h := suffix.length_le
        simp only [List.length_cons] at h
        omega
      by_cases selected : (cutIds sites).contains record.site = true
      · simp only [stripped, selected, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at first
        cases failure : cutFailure record with
        | some message =>
          simp only [failure] at first
          right
          refine ⟨message, ?_, ⟨record, suffix.subset (by simp), passive, selected, failure⟩, ?_⟩
          · simp only [cutLoop, List.forIn_cons, StateT.run_bind, first]
            rfl
          · rw [← cutAccepted_drop sites records, stripped]
            simp only [CutAccepted, passive, Bool.false_eq_true, selected, ↓reduceIte, failure, reduceCtorEq, false_and, not_false_eq_true]
        | none =>
          simp only [failure] at first
          have nextHidden : (cutAdvanced w rest record.site).hidden = some rest := by
            unfold cutAdvanced; split <;> rfl
          have nextSteps : (cutAdvanced w rest record.site).steps = w.steps := by
            unfold cutAdvanced; split <;> rfl
          have nextEnough : rest.length + 1 ≤ turns.length := by
            simp only [List.length_cons] at enough
            omega
          rcases ih (cutAdvanced w rest record.site) rest (taken ++ [record.site]) nextHidden nextEnough with
            ⟨extra, tail, final, execution, hidden, steps, progress⟩ |
            ⟨message, execution, bad, rejected⟩
          · left
            refine ⟨record.site :: extra, tail, final, ?_, hidden, steps.trans nextSteps, ?_⟩
            · simp only [cutLoop, List.forIn_cons, StateT.run_bind, first]
              change (cutLoop sites turns (taken ++ [record.site])).run (cutAdvanced w rest record.site) = _
              simpa [List.append_assoc] using execution
            · exact cutProgress_prepend sites records rest tail record.site extra suffixRest shorter
                (by simpa using selected) progress
          · right
            refine ⟨message, ?_, ?_, ?_⟩
            · simp only [cutLoop, List.forIn_cons, StateT.run_bind, first]
              change (cutLoop sites turns (taken ++ [record.site])).run (cutAdvanced w rest record.site) = _
              simpa [nextSteps] using execution
            · obtain ⟨badRecord, member, notPassive, chosen, failed⟩ := bad
              exact ⟨badRecord, suffixRest.subset member, notPassive, chosen, failed⟩
            · rw [← cutAccepted_drop sites records, stripped]
              simp only [CutAccepted, passive, Bool.false_eq_true, selected, ↓reduceIte, failure, true_and]; exact rejected
      · have notSelected : (cutIds sites).contains record.site = false := by simpa using selected
        simp only [stripped, notSelected, Bool.not_false, ↓reduceIte] at first
        left
        refine ⟨[], record :: rest, { w with hidden := some (record :: rest) }, ?_, rfl, rfl, ?_⟩
        · simp only [cutLoop, List.forIn_cons, StateT.run_bind, first, List.append_nil]
          rfl
        · exact ⟨suffix, by simpa using suffix.length_le, by simp, passive, notSelected⟩

/-- The original budget is measured before ambient stripping, and includes
the final iteration that observes an empty or non-cut head. -/
theorem skipCutSites_outcome (sites : List HiddenSite) (w : Ambient)
    (records : List HiddenRecord) (present : w.hidden = some records) :
    (∃ taken rest final, (AmbientM.skipCutSites sites).run w = .ok (taken, final) ∧
      final.hidden = some rest ∧ CutProgress sites records taken rest) ∨
    (∃ message, (AmbientM.skipCutSites sites).run w =
      .error (.outsideDomain (cutErrorLocation w.steps) message) ∧
      CutFailure sites records message ∧ ¬ CutAccepted sites records) := by
  have budget : AmbientM.recordBudget.run w = .ok (records.length + 1, w) := by
    change Except.ok ((match w.hidden with | some rs => rs.length + 1 | none => DOMAIN_FILTER_TURNS), w) = _
    rw [present]
  have source : (AmbientM.skipCutSites sites).run w =
      ((cutLoop sites (List.range' 0 (records.length + 1)) []).run w >>= fun out =>
        (cutFinish out.1).run out.2) := by
    rw [skipCutSites_source, StateT.run_bind, budget]
    change ((forIn ([:records.length + 1] : Std.Legacy.Range) (none, []) (cutStep sites)).run w >>=
      fun out => (cutFinish out.1).run out.2) = _
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp [cutLoop]
  rcases cutLoop_outcome sites (List.range' 0 (records.length + 1)) w records [] present (by simp) with
    ⟨taken, rest, final, execution, hidden, _, progress⟩ |
    ⟨message, execution, bad, rejected⟩
  · left
    refine ⟨taken, rest, final, ?_, hidden, progress⟩
    rw [source, execution]
    rfl
  · right
    exact ⟨message, by rw [source, execution]; rfl, bad, rejected⟩

end Leanux.Proofs.WG.Progress
