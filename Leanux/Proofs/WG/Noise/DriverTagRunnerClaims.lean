import Leanux.Proofs.WG.Noise.DriverTagRunnerSource
import Leanux.Proofs.WG.Noise.DriverTagStateModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration Origins.HistorySupport Std.Do

def inspection (call : Syscall → ProductObs Int) (trace : Trace) (placeholders : Bool) : Inspection :=
  let out := runPrefixOuter (observed call trace placeholders) []
  (out.1.map (fun (j,w) => (j,Campaign2.snapshot w.wg w.ambient)),out.2)

theorem facts (call : Syscall → ProductObs Int)
    (calls : ∀ c, PrefixPreserves (StateInv emptyTags) ValidHistory (call c))
    (trace : Trace) (placeholders : Bool) :
    Facts (inspection call trace placeholders) := by
  refine ⟨history call calls trace placeholders,?_⟩
  cases run : runPrefixOuter (observed call trace placeholders) [] with
  | mk out h =>
    cases out with
    | error stop => simp only [inspection,run,Except.map]
    | ok out =>
      obtain ⟨j,w⟩ := out
      have good := normal call calls trace placeholders j w h run
      simpa only [inspection,run,Except.map,snapshot_tags,NativeCoverage] using good.1

theorem inspection_json (call : Syscall → ProductObs Int)
    (calls : ∀ c, ErasesPrefix (call c) (Leanux.syscall c))
    (trace : Trace) (placeholders : Bool) :
    (inspection call trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders := by
  have same := json call calls trace placeholders []
  cases run : (runPrefixOuter (observed call trace placeholders) []).1 <;>
    simpa only [inspection,run,Except.map] using same

/-- A normal initialized result has only the five named handshake states.
Every surviving tag appears after an actual valid recorded helper or birth;
the empty initial device supplies no unexplained initial tag. -/
theorem Facts.normal_summary {out : Inspection} (facts : Facts out)
    {json : Json} {final : Campaign2.Snapshot}
    (normal : out.1 = .ok (json,final)) :
    HandshakeTags final.tagAt ∧
      ∀ pid tag, final.tagAt pid = some tag →
        ∃ event ∈ out.2, EventValid event ∧ event.Effect ∧
          event.after.tagAt pid = some tag := by
  have coverage : DriverTagMapCoverage emptyTags out.2 final.tagAt := by
    simpa only [normal] using facts.2
  refine ⟨coverage.initialized_handshakeTags,?_⟩
  intro pid tag present
  rcases coverage.surviving_origin pid tag present with initial | ⟨event,member,origin⟩
  · cases initial
  · exact ⟨event,member,facts.1 event member,event_effect (facts.1 event member),origin⟩

end Leanux.Proofs.WG.Noise.DriverTags.Initialized
