import Leanux.Proofs.WG.TimerDiscipline.Model

/-! Finite supplied-record resolution for the two original timer jitter sites.
Each successful read consumes a strict suffix, including passive skips. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.TimerDiscipline

def resolveJitterInput (site : JitterSite) (records : List HiddenRecord) : Except Stop (List UInt8 × List HiddenRecord) :=
  let info := site.hiddenSite.info
  match records.dropWhile (fun r => HiddenSite.passive r.site) with
  | [] => .error (.hidden s!"no record left for {info.label}")
  | r :: rest =>
    if r.site != info.id then
      .error (.hidden s!"expected {info.label} (site {info.id}), the record is site {r.site}")
    else if r.bytes.length != 8 * ((info.len + 7) / 8) || (r.bytes.drop info.len).any (· != 0) then
      .error (.hidden s!"{info.label}: {r.bytes.length} bytes, expected {info.len} padded to {8 * ((info.len + 7) / 8)}")
    else .ok (r.bytes.take info.len, rest)

theorem resolveJitterInput_suffix (site : JitterSite) (records : List HiddenRecord) (bytes : List UInt8)
    (rest : List HiddenRecord) (run : resolveJitterInput site records = .ok (bytes, rest)) :
    rest.IsSuffix records ∧ rest.length < records.length := by
  unfold resolveJitterInput at run
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

theorem resolveJitterInput_error (site : JitterSite) (records : List HiddenRecord) (error : Stop)
    (h : resolveJitterInput site records = .error error) :
    ∃ message, error = .hidden message := by
  unfold resolveJitterInput at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h


def resolveJitterSearch (site : JitterSite) (records : List HiddenRecord) :
    Except Stop (Nat × List HiddenRecord) :=
  match hr : resolveJitterInput site records with
  | .error error => .error error
  | .ok (bytes, rest) =>
    if jitterAccepted bytes[0]! then .ok (jitterValue bytes[0]!, rest)
    else resolveJitterSearch site rest
termination_by records.length
decreasing_by exact (resolveJitterInput_suffix site records bytes rest hr).2

theorem resolveJitterSearch_outcome (site : JitterSite) (records : List HiddenRecord) :
    match resolveJitterSearch site records with
    | .error error => ∃ message, error = .hidden message
    | .ok (jitter, rest) =>
      jitter < HZ / 3 ∧ rest.IsSuffix records ∧ rest.length < records.length := by
  rw [resolveJitterSearch]
  cases h : resolveJitterInput site records with
  | error error =>
    exact resolveJitterInput_error site records error h
  | ok pair =>
    rcases pair with ⟨bytes, rest⟩
    dsimp only
    have suffix := resolveJitterInput_suffix site records bytes rest h
    by_cases accepted : jitterAccepted bytes[0]!
    · rw [ite_eq_left accepted]
      refine ⟨?_, suffix⟩
      have byteBound := UInt8.toNat_lt_size bytes[0]!
      unfold jitterValue HZ
      change _ < 256 at byteBound
      omega
    · rw [ite_eq_right accepted]
      have ih := resolveJitterSearch_outcome site rest
      cases outcome : resolveJitterSearch site rest with
      | error error => simpa [outcome] using ih
      | ok pair =>
        rcases pair with ⟨jitter, tail⟩
        simp only [outcome] at ih ⊢
        exact ⟨ih.1, ih.2.1.trans suffix.1, Nat.lt_trans ih.2.2 suffix.2⟩
termination_by records.length
decreasing_by exact (resolveJitterInput_suffix site records bytes rest h).2
end Leanux.Proofs.WG.Progress
