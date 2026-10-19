import Leanux.Proofs.WG.Roaming.HandshakeAttemptModel
import Leanux.Proofs.WG.Roaming.HandshakeAttemptAuthSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttempts
open Leanux Leanux.WG Leanux.Proofs.Logged

def initiation (msg : List UInt8) (src : SkbSource) :
    WGPrefix (Attempt InitiationCallCut) Unit :=
  HandshakeAttemptAuth.callObserved (initiationCallPrefix msg src)
    (fun cut => cut.consumed.pid)
    (fun cut => initiationAfterSetter msg cut.consumed.pid) src
    (fun cut endpoint g ambient => ⟨cut,endpoint,Campaign2.snapshot g ambient⟩)

def response (msg : List UInt8) (src : SkbSource) :
    WGPrefix (Attempt ResponseCallCut) Unit :=
  HandshakeAttemptAuth.callObserved (responseCallPrefix msg src)
    (fun cut => cut.consumed.input.pid)
    (fun cut => responseAfterSetter msg cut.consumed.input.pid) src
    (fun cut endpoint g ambient => ⟨cut,endpoint,Campaign2.snapshot g ambient⟩)

/-- Inspect one actual instrumented call, retaining its reached setter
attempts on Stop and returning the unchanged inspection entry. -/
def inspect {E : Type} (observed : WGPrefix E Unit) : WG.M (Audit E) :=
  fun g ambient =>
    let run := runWGPrefix observed g ambient []
    .ok ((⟨run.2,Campaign2.observeResult run.1⟩,g),ambient)

def observeInitiation (msg : List UInt8) (src : SkbSource) :=
  inspect (initiation msg src)

def observeResponse (msg : List UInt8) (src : SkbSource) :=
  inspect (response msg src)

theorem inspect_facts {E : Type} (observed : WGPrefix E Unit) (facts : E → Prop)
    (checked : StatePrefixPreserves
      (fun h _ _ => HandshakeAttemptAuth.ValidHistory facts h)
      (HandshakeAttemptAuth.ValidHistory facts) observed) :
    Campaign2.Observes (inspect observed) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, facts attempt) := by
  intro g ambient _
  refine ⟨⟨(runWGPrefix observed g ambient []).2,
    Campaign2.observeResult (runWGPrefix observed g ambient []).1⟩,rfl,?_⟩
  exact (checked g ambient [] (by intro e member; cases member)).choose_spec.2.1

theorem inspect_original {E : Type} (observed : WGPrefix E Unit) (original : WG.M Unit)
    (erases : ErasesStatePrefix observed original) :
    (do let audited ← inspect observed; pure audited.outcome) = Campaign2.inspect original := by
  funext g ambient
  change (Except.ok ((Campaign2.observeResult (runWGPrefix observed g ambient []).1,g),ambient) :
    Except Stop ((Campaign2.Outcome Unit × WGWorld) × Ambient)) =
    .ok ((Campaign2.observeResult ((original.run g).run ambient),g),ambient)
  have erased : (runWGPrefix observed g ambient []).1 = ((original.run g).run ambient) :=
    erases g ambient []
  rw [erased]

end Leanux.Proofs.WG.Roaming.HandshakeAttempts
