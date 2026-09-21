import Leanux.Reference.EventfdRead

namespace Leanux.Reference.EventfdRead

/-- Fixed stepping obligation, parameterized only by the two candidate helpers.
All counters, flag words, and initial output slots admitted by EntryRelated are
quantified; the source context is explicit and independently inhabited. -/
def StepSimulation
    (readValue : Leanux.FS.Eventfd.Ctx → UInt64)
    (doRead : Leanux.FS.Eventfd.Ctx → Leanux.FS.Eventfd.ReadResult) : Prop :=
  ∀ (context : SourceContext) (s : State) (m : Leanux.FS.Eventfd.Ctx),
    AdmittedContext context → EntryRelated s m →
      step s = some (assignOutput s) ∧
      AssignedRelated (assignOutput s) m (readValue m) ∧
      step (assignOutput s) = some (run s) ∧
      ExitRelated (run s) (doRead m) ∧
      EffectsRelated (effects s) (doRead m) ∧
      (run s).flags = s.flags ∧
      (doRead m).next.semaphore = m.semaphore ∧
      step (run s) = none

end Leanux.Reference.EventfdRead
