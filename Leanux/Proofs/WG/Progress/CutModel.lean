import Leanux.Proofs.WG.Campaign2.View

namespace Leanux.Proofs.WG.Progress
open Leanux Campaign2

def cutIds (sites : List HiddenSite) : List Nat := sites.map (·.info.id)

/-- The original cut's allocation test: no byte-length check, and an empty
payload has the successful default byte 1. -/
def cutFailure (record : HiddenRecord) : Option String :=
  match (AllocSite.cuts.map fun s => (HiddenSite.alloc s).info).find? (·.id == record.site) with
  | none => none
  | some info => if record.bytes.headD 1 != 1 then
      some s!"a below-cut allocation failed ({info.label}, {info.file}:{info.line})"
    else none

/-- Only the consumed prefix is constrained. Passive records are skipped;
the first non-passive record outside the selected sites ends the cut. -/
def CutAccepted (sites : List HiddenSite) : List HiddenRecord → Prop
  | [] => True
  | record :: rest =>
    if HiddenSite.passive record.site then CutAccepted sites rest
    else if (cutIds sites).contains record.site then
      cutFailure record = none ∧ CutAccepted sites rest
    else True

def CutStopped (sites : List HiddenSite) : List HiddenRecord → Prop
  | [] => True
  | record :: _ => HiddenSite.passive record.site = false ∧
      (cutIds sites).contains record.site = false

/-- Every reported site costs a record; ambient records can consume additional
input. The untouched trailing records are an actual suffix. -/
def CutProgress (sites : List HiddenSite) (input : List HiddenRecord)
    (taken : List Nat) (rest : List HiddenRecord) : Prop :=
  rest.IsSuffix input ∧ taken.length + rest.length ≤ input.length ∧
  (∀ site ∈ taken, site ∈ cutIds sites) ∧ CutStopped sites rest

def CutFailure (sites : List HiddenSite) (input : List HiddenRecord) (message : String) : Prop :=
  ∃ record ∈ input, HiddenSite.passive record.site = false ∧
    (cutIds sites).contains record.site = true ∧ cutFailure record = some message

def cutErrorLocation (steps : Array Step) : String :=
  match steps.back? with
  | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
  | none => "syscall entry"

/-- Exact outcome classes of the recorded cut, excluding fuel exhaustion.
Allocation failures retain the original error location and message. -/
def CutOutcome (sites : List HiddenSite) (input : List HiddenRecord)
    (entry : Snapshot) : Outcome (List Nat) → Prop
  | .ok (taken, final) => ∃ rest, final.ambient.hidden = some rest ∧ CutProgress sites input taken rest
  | .error err => ∃ message, err = .outsideDomain (cutErrorLocation entry.ambient.steps) message ∧
      CutFailure sites input message

theorem cutAccepted_drop (sites : List HiddenSite) (records : List HiddenRecord) :
    CutAccepted sites (records.dropWhile fun r => HiddenSite.passive r.site) = CutAccepted sites records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    by_cases passive : HiddenSite.passive record.site = true
    · simpa [List.dropWhile_cons, passive, CutAccepted] using ih
    · simp [passive]

theorem cutProgress_prepend (sites : List HiddenSite) (input middle rest : List HiddenRecord)
    (site : Nat) (taken : List Nat)
    (suffixInput : middle.IsSuffix input) (shorter : middle.length < input.length)
    (selected : site ∈ cutIds sites) (tail : CutProgress sites middle taken rest) :
    CutProgress sites input (site :: taken) rest := by
  obtain ⟨suffix, size, members, stopped⟩ := tail
  exact ⟨suffix.trans suffixInput, by simp only [List.length_cons]; omega,
    by intro value member; rcases List.mem_cons.mp member with rfl | old
       · exact selected
       · exact members value old, stopped⟩

end Leanux.Proofs.WG.Progress
