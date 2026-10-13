import Leanux.Proofs.Logged.Basic

/-! Public proof-side names for the pinned private allocation helpers.
The equation below checks the entire copy by definitional equality. -/
namespace Leanux.Proofs.Framing.Allocation
open Leanux

def recordOutcome (s : AllocSite) : M Bool := do
  let bs ← hidden (.alloc s)
  match bs.headD 2 with
  | 1 => return true
  | 0 => return false
  | b => throw (.hidden s!"{s.info.label}: outcome byte {b}, expected 0 or 1")

/-- One allocation encounter's outcome in the domain filter (placeholders):
    ok, unless the steering schedule names the site, in which case its next
    entry decides (a draw is ok; the only value is the fail word). -/
def placeholderOutcome (s : AllocSite) : M Bool := do
  let w ← get
  match w.steerValues.findIdx? (·.1 == s.info.label) with
  | none =>
    -- the kernel would record this encounter of a named site against no
    -- entry: the schedule must list every encounter
    if w.allocSteered.contains s.info.label then
      unsupported s!"steer: an encounter of {s.info.label} beyond its schedule"
    return true
  | some k =>
    set { w with steerValues := w.steerValues.eraseIdx k }
    match w.steerValues[k]!.2 with
    | none => return true
    | some v =>
      if v.length != 8 || v.any (· != 0) then throw (.hidden s!"steer: {s.info.label} takes draw or the fail word")
      return false

/-- An allocation outcome at this consumer frame (design section 6.1): `ok`,
    or the failure arm.
    - An exact site consumes its declared number of records, in order, and
      stops at a failed one (an `__alloc_skb` site: the `sk_buff`, then the
      data buffer). A missing, unexpected or malformed record is a hidden
      mismatch, as for every choice.
    - A lax site with count 0 answers ok and consumes nothing (A0 found no
      allocation there on this fixture, section 16.2.3): a record of it
      would be left over, failing the run.
    - A site the run did not arm answers ok: the transitional unarmed
      answer (section 6.6), declared in `World.allocArmed`.
    In the domain filter the steering schedule decides (`allocPlaceholder`). -/
def allocationOutcome (s : AllocSite) : M Bool := do
  let i := s.info
  match i.count with
  | .laxZero => return true
  | .unrecorded => return true
  | .cut => invariant s!"{i.label} is a below-cut consumer, consumed only at a cut point"
  | .exact n =>
    let w ← get
    let placeholders := w.hidden.isNone && w.hiddenPlaceholders
    if !placeholders && !w.allocArmed.contains i.label then return true   -- unarmed (section 6.6)
    let encounter : M Bool := if placeholders then placeholderOutcome s else recordOutcome s
    let mut k := 0
    while k < n do
      if !(← encounter) then return false
      k := k + 1
    return true

theorem allocationOutcome_eq (s : AllocSite) :
    allocationOutcome s = hiddenAlloc s := rfl

end Leanux.Proofs.Framing.Allocation
