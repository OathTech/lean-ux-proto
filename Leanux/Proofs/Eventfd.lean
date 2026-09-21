import Leanux.Reference.EventfdContract
import Leanux.FS.Eventfd

namespace Leanux.Proofs

open Reference.EventfdRead

/-- Both assignments and their effects agree for every related fixed-width
    state. The source-context witness documents the restricted source bridge;
    this theorem concerns the two Lean encodings, not a semantics of kernel C. -/
theorem eventfd_step_simulation :
    StepSimulation FS.Eventfd.readValue FS.Eventfd.eventfdCtxDoRead := by
  intro context s m _admitted related
  rcases related with ⟨pc, count, semaphore⟩
  simp [step, pc, AssignedRelated, FieldsRelated, assignOutput, selectOutput,
    run, subtractOutput, ExitRelated, EffectsRelated, effects,
    FS.Eventfd.eventfdCtxDoRead, FS.Eventfd.readValue, count, semaphore]

end Leanux.Proofs
