import Leanux.Kernel.Defs

/-! Pure recorded-control and log-sequence facts, independent of queue representation.
Native activation/snapshot correspondence remains in CookieActivationModel. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

def cookieControlSite (yielded : Bool) : HiddenSite :=
  if yielded then .reschedReceive else .sectionStop .receiveWorker

def resolveCookieRead (yielded : Bool) (records : List HiddenRecord) :
    Except Stop (List UInt8 × List HiddenRecord) :=
  let info := (cookieControlSite yielded).info
  match records.dropWhile (fun r => HiddenSite.passive r.site) with
  | [] => .error (.hidden s!"no record left for {info.label}")
  | r :: rest =>
    if r.site != info.id then
      .error (.hidden s!"expected {info.label} (site {info.id}), the record is site {r.site}")
    else if r.bytes.length != 8 * ((info.len + 7) / 8) ||
        (r.bytes.drop info.len).any (· != 0) then
      .error (.hidden s!"{info.label}: {r.bytes.length} bytes, expected {info.len} padded to {8 * ((info.len + 7) / 8)}")
    else .ok (r.bytes.take info.len, rest)

def cookieNext (records : List HiddenRecord) : Option Nat :=
  ((records.dropWhile fun r => HiddenSite.passive r.site).head?).map (·.site)

def cookieReschedResult (records : List HiddenRecord) :
    Except Stop (Bool × List HiddenRecord) :=
  let stripped := records.dropWhile fun r => HiddenSite.passive r.site
  if cookieNext records = some HiddenSite.reschedReceive.info.id then
    match resolveCookieRead true stripped with
    | .error error => .error error
    | .ok (_, rest) => .ok (true, rest)
  else .ok (false, stripped)

structure CookieActivationSummary where
  processed : Nat
  yielded : Bool
  rest : List HiddenRecord

def cookieIncrement (out : Except Stop CookieActivationSummary) :
    Except Stop CookieActivationSummary :=
  out.map fun summary => {summary with processed := summary.processed + 1}

def resolveCookieActivation : Nat → List HiddenRecord → Except Stop CookieActivationSummary
  | 0, records =>
    match resolveCookieRead false records with
    | .error error => .error error
    | .ok (_, rest) => .ok ⟨0, false, rest⟩
  | count + 1, records =>
    match cookieReschedResult records with
    | .error error => .error error
    | .ok (true, rest) => .ok ⟨1, true, rest⟩
    | .ok (false, rest) => cookieIncrement (resolveCookieActivation count rest)

theorem resolveCookieRead_suffix (yielded : Bool) (records : List HiddenRecord)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (run : resolveCookieRead yielded records = .ok (bytes, rest)) :
    rest.IsSuffix records ∧ rest.length < records.length := by
  unfold resolveCookieRead at run
  cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil => simp [stripped] at run
  | cons record tail =>
    simp only [stripped] at run
    split at run
    · cases run
    · split at run
      · cases run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have suffix := List.dropWhile_suffix (l := records) (fun r => HiddenSite.passive r.site)
        rw [stripped] at suffix
        refine ⟨(List.suffix_cons record tail).trans suffix, ?_⟩
        have bound := suffix.length_le
        simp only [List.length_cons] at bound
        omega

theorem resolveCookieRead_error (yielded : Bool) (records : List HiddenRecord) (error : Stop)
    (run : resolveCookieRead yielded records = .error error) :
    ∃ message, error = .hidden message := by
  unfold resolveCookieRead at run
  dsimp only at run
  split at run
  · cases run; exact ⟨_, rfl⟩
  · split at run
    · cases run; exact ⟨_, rfl⟩
    · split at run
      · cases run; exact ⟨_, rfl⟩
      · cases run

theorem cookieReschedResult_suffix (records : List HiddenRecord) (yielded : Bool)
    (rest : List HiddenRecord) (run : cookieReschedResult records = .ok (yielded, rest)) :
    rest.IsSuffix records ∧ (yielded = true → rest.length < records.length) := by
  unfold cookieReschedResult at run
  split at run
  · cases input : resolveCookieRead true
        (records.dropWhile fun r => HiddenSite.passive r.site) with
    | error error => simp [input] at run
    | ok pair =>
      rcases pair with ⟨bytes, tail⟩
      simp only [input, Except.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have consumed := resolveCookieRead_suffix true _ bytes tail input
      have stripped := List.dropWhile_suffix (l := records) (fun r => HiddenSite.passive r.site)
      exact ⟨consumed.1.trans stripped, fun _ => Nat.lt_of_lt_of_le consumed.2 stripped.length_le⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨List.dropWhile_suffix (l := records) _, by simp⟩

theorem cookieReschedResult_error (records : List HiddenRecord) (error : Stop)
    (run : cookieReschedResult records = .error error) :
    ∃ message, error = .hidden message := by
  unfold cookieReschedResult at run
  split at run
  · cases input : resolveCookieRead true
        (records.dropWhile fun r => HiddenSite.passive r.site) with
    | error err =>
      simp only [input, Except.error.injEq] at run
      subst error
      exact resolveCookieRead_error true _ err input
    | ok pair => simp [input] at run
  · cases run

def CookieActivationProgress (count : Nat) (records : List HiddenRecord)
    (summary : CookieActivationSummary) : Prop :=
  summary.processed ≤ count ∧
  (summary.yielded = true → 0 < summary.processed) ∧
  (summary.yielded = false → summary.processed = count) ∧
  summary.rest.IsSuffix records ∧ summary.rest.length < records.length

theorem resolveCookieActivation_progress (count : Nat) (records : List HiddenRecord) :
    match resolveCookieActivation count records with
    | .error error => ∃ message, error = .hidden message
    | .ok summary => CookieActivationProgress count records summary := by
  induction count generalizing records with
  | zero =>
    unfold resolveCookieActivation
    cases input : resolveCookieRead false records with
    | error error => exact resolveCookieRead_error false records error input
    | ok pair =>
      rcases pair with ⟨bytes, rest⟩
      have consumed := resolveCookieRead_suffix false records bytes rest input
      exact ⟨Nat.zero_le _, by simp, by simp, consumed⟩
  | succ count ih =>
    unfold resolveCookieActivation
    cases head : cookieReschedResult records with
    | error error => exact cookieReschedResult_error records error head
    | ok pair =>
      rcases pair with ⟨yielded, rest⟩
      have suffix := cookieReschedResult_suffix records yielded rest head
      cases yielded with
      | true =>
        exact ⟨by simp, by simp, by simp, suffix.1, suffix.2 rfl⟩
      | false =>
        have tail := ih rest
        cases result : resolveCookieActivation count rest with
        | error error => simpa [cookieIncrement, result, Except.map] using tail
        | ok summary =>
          simp only [result] at tail
          rcases tail with ⟨bound, positive, ended, suffixTail, shorter⟩
          simp only [cookieIncrement, result, Except.map]
          change CookieActivationProgress (count + 1) records
            {summary with processed := summary.processed + 1}
          exact ⟨Nat.succ_le_succ bound, by simp, fun h => by have same := ended h; simp [same],
            suffixTail.trans suffix.1, Nat.lt_of_lt_of_le shorter suffix.1.length_le⟩

theorem cookie_drop_idem (records : List HiddenRecord) :
    (records.dropWhile fun r => HiddenSite.passive r.site).dropWhile
      (fun r => HiddenSite.passive r.site) =
      records.dropWhile (fun r => HiddenSite.passive r.site) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    cases passive : HiddenSite.passive record.site <;> simp [passive, ih]

theorem cookieNext_drop (records : List HiddenRecord) :
    cookieNext (records.dropWhile fun r => HiddenSite.passive r.site) = cookieNext records := by
  unfold cookieNext
  rw [cookie_drop_idem]

theorem cookieReschedResult_false (records rest : List HiddenRecord)
    (run : cookieReschedResult records = .ok (false, rest)) :
    rest = records.dropWhile (fun r => HiddenSite.passive r.site) ∧
      cookieNext rest ≠ some HiddenSite.reschedReceive.info.id := by
  unfold cookieReschedResult at run
  split at run
  · cases input : resolveCookieRead true
        (records.dropWhile fun r => HiddenSite.passive r.site) <;> simp [input] at run
  · rename_i different
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at run
    subst rest
    exact ⟨rfl, by simpa [cookieNext_drop] using different⟩

theorem resolveCookieActivation_no_yield (count : Nat) (records : List HiddenRecord)
    (notResched : cookieNext records ≠ some HiddenSite.reschedReceive.info.id)
    (summary : CookieActivationSummary)
    (run : resolveCookieActivation count records = .ok summary) :
    summary.yielded = false := by
  induction count generalizing records summary with
  | zero =>
    unfold resolveCookieActivation at run
    cases input : resolveCookieRead false records with
    | error error => simp [input] at run
    | ok pair =>
      rcases pair with ⟨bytes, rest⟩
      simp only [input, Except.ok.injEq] at run
      subst summary
      rfl
  | succ count ih =>
    have head : cookieReschedResult records =
        .ok (false, records.dropWhile fun r => HiddenSite.passive r.site) := by
      simp [cookieReschedResult, notResched]
    simp only [resolveCookieActivation, head, cookieIncrement] at run
    cases tail : resolveCookieActivation count
        (records.dropWhile fun r => HiddenSite.passive r.site) with
    | error error => simp [tail, Except.map] at run
    | ok result =>
      simp only [tail, Except.map, Except.ok.injEq] at run
      subst summary
      exact ih _ (by simpa [cookieNext_drop] using notResched) result tail

theorem resolveCookieActivation_yield_count (count : Nat) (records : List HiddenRecord)
    (summary : CookieActivationSummary)
    (run : resolveCookieActivation count records = .ok summary)
    (yielded : summary.yielded = true) :
    summary.processed = 1 := by
  cases count with
  | zero =>
    have progress := resolveCookieActivation_progress 0 records
    rw [run] at progress
    have impossible := progress.2.1 yielded
    have bound := progress.1
    omega
  | succ count =>
    unfold resolveCookieActivation at run
    cases head : cookieReschedResult records with
    | error error => simp [head] at run
    | ok pair =>
      rcases pair with ⟨rescheduled, rest⟩
      cases rescheduled with
      | true =>
        simp only [head, Except.ok.injEq] at run
        subst summary
        rfl
      | false =>
        have noResched := (cookieReschedResult_false records rest head).2
        simp only [head, cookieIncrement] at run
        cases tail : resolveCookieActivation count rest with
        | error error => simp [tail, Except.map] at run
        | ok result =>
          simp only [tail, Except.map, Except.ok.injEq] at run
          subst summary
          have ended := resolveCookieActivation_no_yield count rest noResched result tail
          simp only at yielded
          rw [ended] at yielded
          cases yielded

def cookiePacketSteps (netRx : Nat) (steps : Array Step) : Array Step :=
  ((((steps.push {decision := .workerConsumed, outcome := true, netRx}).push
    {decision := .hsCookie, outcome := true, netRx}).push
    {decision := .idxWalk, outcome := false, netRx}).push
    {decision := .idxFound, outcome := false, netRx}).push
    {decision := .cookieLookupMiss, outcome := true, netRx}

def cookieProcessedSteps (netRx : Nat) : Nat → Array Step → Array Step
  | 0, steps => steps
  | count + 1, steps => cookieProcessedSteps netRx count (cookiePacketSteps netRx steps)

def cookieFinalSteps (netRx : Nat) (summary : CookieActivationSummary)
    (steps : Array Step) : Array Step :=
  let processed := cookieProcessedSteps netRx summary.processed steps
  if summary.yielded then processed
  else processed.push {decision := .workerConsumed, outcome := false, netRx}

theorem cookieProcessedSteps_add (netRx first second : Nat) (steps : Array Step) :
    cookieProcessedSteps netRx (first + second) steps =
      cookieProcessedSteps netRx second (cookieProcessedSteps netRx first steps) := by
  induction first generalizing steps with
  | zero => simp [cookieProcessedSteps]
  | succ first ih => simpa [Nat.succ_add, cookieProcessedSteps] using ih (cookiePacketSteps netRx steps)

theorem cookieYield_advanced (a : Activation) (count : Nat) (records : List HiddenRecord)
    (summary : CookieActivationSummary)
    (progress : CookieActivationProgress count records summary) (yielded : summary.yielded = true) :
    a.iterations < ({a with iterations := a.iterations + summary.processed} : Activation).iterations := by
  have positive := progress.2.1 yielded
  change a.iterations < a.iterations + summary.processed
  omega


end Leanux.Proofs.WG.Progress
