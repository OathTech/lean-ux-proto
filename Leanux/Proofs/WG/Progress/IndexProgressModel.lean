import Leanux.Proofs.WG.Campaign2.View

/-! Data-only resolution of the original recorded index search. Passive records
are skipped without payload validation, exactly as by the original hidden read.
Freshness is relative to the supplied table; insertion supplies the table after
unhashing its owner. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

def resolveIndexInput (records : List HiddenRecord) : Except Stop (List UInt8 × List HiddenRecord) :=
  let info := HiddenSite.indexDraw.info
  match records.dropWhile (fun r => HiddenSite.passive r.site) with
  | [] => .error (.hidden s!"no record left for {info.label}")
  | r :: rest =>
    if r.site != info.id then
      .error (.hidden s!"expected {info.label} (site {info.id}), the record is site {r.site}")
    else if r.bytes.length != 8 * ((info.len + 7) / 8) || (r.bytes.drop info.len).any (· != 0) then
      .error (.hidden s!"{info.label}: {r.bytes.length} bytes, expected {info.len} padded to {8 * ((info.len + 7) / 8)}")
    else .ok (r.bytes.take info.len, rest)
theorem resolveIndexInput_suffix (records : List HiddenRecord) (bytes : List UInt8)
    (rest : List HiddenRecord) (run : resolveIndexInput records = .ok (bytes, rest)) :
    rest.IsSuffix records ∧ rest.length < records.length := by
  unfold resolveIndexInput at run
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

def resolveIndexSearch (entries : List IndexEntry) (records : List HiddenRecord) :
    Except Stop (Nat × List HiddenRecord) :=
  match hr : resolveIndexInput records with
  | .error error => .error error
  | .ok (bytes, rest) =>
    let index := bytes.foldr (fun b acc => acc * 256 + b.toNat) 0
    if entries.any (·.index == index) then resolveIndexSearch entries rest
    else .ok (index, rest)
termination_by records.length
decreasing_by exact (resolveIndexInput_suffix records bytes rest hr).2

theorem resolveIndexInput_error (records : List HiddenRecord) (error : Stop)
    (h : resolveIndexInput records = .error error) :
    ∃ message, error = .hidden message := by
  unfold resolveIndexInput at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h

theorem resolveIndexSearch_outcome (entries : List IndexEntry) (records : List HiddenRecord) :
    match resolveIndexSearch entries records with
    | .error error => ∃ message, error = .hidden message
    | .ok (index, rest) =>
      entries.any (·.index == index) = false ∧ rest.IsSuffix records ∧ rest.length < records.length := by
  rw [resolveIndexSearch]
  cases h : resolveIndexInput records with
  | error error =>
    dsimp only
    exact resolveIndexInput_error records error h
  | ok pair =>
    rcases pair with ⟨bytes, rest⟩
    dsimp only
    have suffix := resolveIndexInput_suffix records bytes rest h
    by_cases collision : entries.any (·.index == bytes.foldr (fun b acc => acc * 256 + b.toNat) 0) = true
    · rw [ite_eq_left collision]
      have ih := resolveIndexSearch_outcome entries rest
      cases outcome : resolveIndexSearch entries rest with
      | error error => simpa [outcome] using ih
      | ok pair =>
        rcases pair with ⟨index, tail⟩
        simp only [outcome] at ih ⊢
        exact ⟨ih.1, ih.2.1.trans suffix.1, Nat.lt_trans ih.2.2 suffix.2⟩
    · rw [ite_eq_right collision]
      exact ⟨by simpa using collision, suffix⟩
termination_by records.length
decreasing_by exact (resolveIndexInput_suffix records bytes rest h).2



end Leanux.Proofs.WG.Progress
