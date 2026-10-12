import Leanux.Seccomp.Decisions

/-!
# A self-contained `SeccompM` instance

The checker and the translation run here without the kernel state: the
unit tests, the executable check of design section 8, and the measurements
of section 11 step 0 use it. It records every step, answers allocation
sites from an injected failure list, and serves kind-309 records from a
list. It stops where the mirror would stop.
-/

namespace Leanux.Seccomp.Local

structure LStep where
  decision : SDecision
  outcome : Bool
  operands : Option (Int × Int) := none
  deriving Repr, BEq

inductive LStop where
  | hidden (what : String)
  | outsideDomain (what : String)
  | invariant (what : String)
  deriving Repr, BEq

def LStop.message : LStop → String
  | .hidden w => s!"records disagree: {w}"
  | .outsideDomain w => s!"unsupported: {w}"
  | .invariant w => s!"mirror invariant violated: {w}"

structure LState where
  steps : Array LStep := #[]
  /-- Recorded sites whose next encounter answers `false` (an injected
      `-ENOMEM`); each entry is consumed once. -/
  failSites : List SAllocSite := []
  /-- The kind-309 words in order (the instructions, then the length);
      `none`: a run without records, as the domain filter. -/
  records : Option (List Nat) := none
  /-- Every allocation answered, in order. -/
  allocs : Array (SAllocSite × Bool) := #[]

abbrev L := StateT LState (Except LStop)

instance : SeccompM L where
  branch d o := do
    modify fun s => { s with steps := s.steps.push { decision := d, outcome := o } }
    return o
  branchCmp d o a b := do
    modify fun s => { s with steps := s.steps.push { decision := d, outcome := o, operands := some (a, b) } }
    return o
  alloc site := do
    let s ← get
    let ok := if site.info.recorded && s.failSites.contains site then false else true
    set { s with failSites := if ok then s.failSites else s.failSites.erase site,
                 allocs := s.allocs.push (site, ok) }
    return ok
  translatedInsn := do
    match (← get).records with
    | none => return none
    | some [] => throw (.hidden "no kind-309 record left for the next translated instruction")
    | some (w :: rest) =>
      modify fun s => { s with records := some rest }
      return some w
  translatedLen := do
    match (← get).records with
    | none => return none
    | some [] => throw (.hidden "no kind-309 record left for the translated length")
    | some (w :: rest) =>
      modify fun s => { s with records := some rest }
      return some w
  recordMismatch what := throw (.hidden what)
  unsupported what := throw (.outsideDomain what)
  invariant what := throw (.invariant what)

/-- Run a walker from a state (empty by default): the result and the final
    state, or the stop. -/
def run (x : L α) (st : LState := {}) : Except LStop (α × LState) := x.run st

/-- The labels of the steps, `label=0/1`, for the tests' spot checks. -/
def LState.labels (s : LState) : List String :=
  s.steps.toList.map fun st => s!"{st.decision.info.label}={if st.outcome then 1 else 0}"

end Leanux.Seccomp.Local
