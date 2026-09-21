import Leanux.FS.EventfdTypes

/-!
An independent, source-shaped encoding of Linux 6.12.110's
`eventfd_ctx_do_read`. The two assignments are separate transitions. This is
not a semantics of C memory, locks, or concurrent kernel execution.
-/
namespace Leanux.Reference.EventfdRead

inductive PC where
  | entry | afterOutput | exit
  deriving Repr, BEq, DecidableEq

structure State where
  flags : UInt32
  count : UInt64
  output : UInt64
  pc : PC
  deriving Repr, BEq, DecidableEq

/-- C's `(ctx->flags & EFD_SEMAPHORE) != 0`, with the configured value 1. -/
def semaphoreEnabled (flags : UInt32) : Bool := (flags &&& 1) != 0

/-- C's conditional expression, independent of every mirror function. -/
def selectOutput (s : State) : UInt64 :=
  if semaphoreEnabled s.flags && s.count != 0 then 1 else s.count

/-- The store to the caller's distinct output slot. -/
def assignOutput (s : State) : State :=
  { s with output := selectOutput s, pc := .afterOutput }

/-- The subsequent store to `ctx->count`, using the assigned output slot. -/
def subtractOutput (s : State) : State :=
  { s with count := s.count - s.output, pc := .exit }

def step (s : State) : Option State :=
  match s.pc with
  | .entry => some (assignOutput s)
  | .afterOutput => some (subtractOutput s)
  | .exit => none

def run (s : State) : State := subtractOutput (assignOutput s)

/-- Preconditions on the source bridge, stated independently of the relation.
These Boolean witnesses document the omitted C context; constructing this
record does not establish the conditions for an actual kernel execution. -/
structure SourceContext where
  lockHeld : Bool
  contextReadableWritable : Bool
  outputWritable : Bool
  storageDisjoint : Bool
  noExternalInterference : Bool
  deriving Repr, BEq, DecidableEq

def AdmittedContext (c : SourceContext) : Prop :=
  c.lockHeld = true ∧ c.contextReadableWritable = true ∧
  c.outputWritable = true ∧ c.storageDisjoint = true ∧
  c.noExternalInterference = true

def FieldsRelated (s : State) (m : Leanux.FS.Eventfd.Ctx) : Prop :=
  s.count = m.count ∧ semaphoreEnabled s.flags = m.semaphore

def EntryRelated (s : State) (m : Leanux.FS.Eventfd.Ctx) : Prop :=
  s.pc = .entry ∧ FieldsRelated s m

/-- The mirror argument is the value actually computed by its readValue helper. -/
def AssignedRelated (s : State) (m : Leanux.FS.Eventfd.Ctx)
    (value : UInt64) : Prop :=
  s.pc = .afterOutput ∧ FieldsRelated s m ∧ s.output = value

/-- Relates both final stores and the unchanged mode. -/
def ExitRelated (s : State) (m : Leanux.FS.Eventfd.ReadResult) : Prop :=
  s.pc = .exit ∧ FieldsRelated s m.next ∧ s.output = m.value

/-- Observable stores of this fragment, before any user-buffer copy. -/
structure Effects where
  outputStore : UInt64
  counterStore : UInt64
  deriving Repr, BEq, DecidableEq

def effects (s : State) : Effects :=
  let final := run s
  ⟨final.output, final.count⟩

def EffectsRelated (e : Effects) (m : Leanux.FS.Eventfd.ReadResult) : Prop :=
  e.outputStore = m.value ∧ e.counterStore = m.next.count

/-- Explicitly inhabited context and all four flag/zero combinations. -/
def exampleContext : SourceContext := ⟨true, true, true, true, true⟩

theorem exampleContext_admitted : AdmittedContext exampleContext := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def ordinaryZero : State := ⟨0, 0, 17, .entry⟩
def ordinaryNonzero : State := ⟨2048, 5, 17, .entry⟩
def semaphoreZero : State := ⟨1, 0, 17, .entry⟩
def semaphoreNonzero : State := ⟨526337, 5, 17, .entry⟩

theorem branch_examples :
    run ordinaryZero = ⟨0, 0, 0, .exit⟩ ∧
    run ordinaryNonzero = ⟨2048, 0, 5, .exit⟩ ∧
    run semaphoreZero = ⟨1, 0, 0, .exit⟩ ∧
    run semaphoreNonzero = ⟨526337, 4, 1, .exit⟩ := by
  decide

end Leanux.Reference.EventfdRead
