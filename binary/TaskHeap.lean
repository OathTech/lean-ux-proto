import TaskLayouts
import Memory
import Leanux.Kernel.Defs

set_option maxRecDepth 4096

namespace Binary.TaskHeap
open Leanux
abbrev Address := BitVec 64

/-- One bit in a native little-endian integer. Other flag bits stay free. -/
def Flag (memory : Mem 64) (address : Address) (width bit : Nat) (value : Bool) : Prop :=
  ∃ word : BitVec (width * 8), memory.loadInt address width = some (word.toNat : Int) ∧
    word.getLsbD bit = value

theorem Flag.functional {memory address width bit first second}
    (hf : Flag memory address width bit first) (hs : Flag memory address width bit second) : first = second := by
  obtain ⟨wf, loadedF, bitF⟩ := hf
  obtain ⟨ws, loadedS, bitS⟩ := hs
  have equal : wf = ws := by
    apply BitVec.eq_of_toNat_eq
    have eq := Option.some.inj (loadedF.symm.trans loadedS)
    omega
  subst ws
  exact bitF.symm.trans bitS

theorem Flag.frame {before after address width bit value writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < width, ¬writes (address + .ofNat 64 i))
    (represented : Flag before address width bit value) : Flag after address width bit value := by
  obtain ⟨word, loaded, bitValue⟩ := represented
  exact ⟨word, (same.loadInt _ _ apart).symm.trans loaded, bitValue⟩

/-- C enum including the force-signal dead mode. -/
def mode : SeccompMode → Nat
  | .disabled => 0 | .strict => 1 | .filter => 2 | .dead => 3

def filterPointer (filters : FilterId → Address) : Option FilterId → Address
  | none => 0 | some id => filters id

/-- The modeled task, not necessarily KCOV current. Constants are the pinned
    PF_KTHREAD, PFA_NO_NEW_PRIVS, TIF_SIGPENDING, CAP_SYS_ADMIN and RLIMIT_NOFILE.
    Task work, SIGSYS disposition, files and filter contents remain separate;
    filter identities still require their allocation/lifetime names. -/
structure Fields (memory : Mem 64) (task cred signal : Address)
    (filters : FilterId → Address) (t : Task) : Prop where
  blocked : memory.loadInt (task + .ofNat 64 TaskLayouts.task_blocked) 8 = some (t.blocked.toBitVec.toNat : Int)
  pending : memory.loadInt (task + .ofNat 64 TaskLayouts.task_pending_signal) 8 = some (t.pending.toBitVec.toNat : Int)
  inEventfd : Flag memory (task + .ofNat 64 TaskLayouts.task_in_eventfd) 4 TaskLayouts.task_in_eventfd_bit t.inEventfd
  isKthread : Flag memory (task + .ofNat 64 TaskLayouts.task_flags) 4 21 t.isKthread
  noNewPrivs : Flag memory (task + .ofNat 64 TaskLayouts.task_atomic_flags) 8 0 t.noNewPrivs
  sigpending : Flag memory (task + .ofNat 64 TaskLayouts.task_thread_info_flags) 8 2 t.sigpending
  credential : memory.loadInt (task + .ofNat 64 TaskLayouts.task_cred) 8 = some (cred.toNat : Int)
  capSysAdmin : Flag memory (cred + .ofNat 64 TaskLayouts.cred_cap_effective) 8 21 t.capSysAdmin
  signalPointer : memory.loadInt (task + .ofNat 64 TaskLayouts.task_signal) 8 = some (signal.toNat : Int)
  rlimitNofile : memory.loadInt (signal + .ofNat 64 (TaskLayouts.signal_rlim + 7 * TaskLayouts.rlimitSize + TaskLayouts.rlimit_rlim_cur)) 8 = some (t.rlimitNofile : Int)
  seccompMode : memory.loadInt (task + .ofNat 64 TaskLayouts.task_seccomp_mode) 4 = some (mode t.seccomp.mode : Int)
  seccompCount : memory.loadInt (task + .ofNat 64 TaskLayouts.task_seccomp_filter_count) 4 = some (t.seccomp.filterCount : Int)
  seccompFilter : memory.loadInt (task + .ofNat 64 TaskLayouts.task_seccomp_filter) 8 = some ((filterPointer filters t.seccomp.filter).toNat : Int)

inductive Base where
  | task | cred | signal
  deriving DecidableEq

def Base.address (task cred signal : Address) : Base → Address
  | .task => task | .cred => cred | .signal => signal

def offsets : List (Base × Nat × Nat) :=
  [(.task, TaskLayouts.task_blocked, 8),
   (.task, TaskLayouts.task_pending_signal, 8),
   (.task, TaskLayouts.task_in_eventfd, 4),
   (.task, TaskLayouts.task_flags, 4),
   (.task, TaskLayouts.task_atomic_flags, 8),
   (.task, TaskLayouts.task_thread_info_flags, 8),
   (.task, TaskLayouts.task_cred, 8),
   (.cred, TaskLayouts.cred_cap_effective, 8),
   (.task, TaskLayouts.task_signal, 8),
   (.signal, (TaskLayouts.signal_rlim + 7 * TaskLayouts.rlimitSize + TaskLayouts.rlimit_rlim_cur), 8),
   (.task, TaskLayouts.task_seccomp_mode, 4),
   (.task, TaskLayouts.task_seccomp_filter_count, 4),
   (.task, TaskLayouts.task_seccomp_filter, 8)]

def location (task cred signal : Address) (spec : Base × Nat × Nat) : Address × Nat :=
  (spec.1.address task cred signal + .ofNat 64 spec.2.1, spec.2.2)

def locations (task cred signal : Address) : List (Address × Nat) :=
  offsets.map (location task cred signal)

private theorem separated {writes : Address → Prop} (task cred signal : Address)
    (apart : ∀ cell ∈ locations task cred signal, ∀ i < cell.2, ¬writes (cell.1 + .ofNat 64 i))
    (base : Base) (off width : Nat) (member : (base, off, width) ∈ offsets) :
    ∀ i < width, ¬writes (base.address task cred signal + .ofNat 64 off + .ofNat 64 i) :=
  apart _ (List.mem_map_of_mem (f := location task cred signal) member)

private theorem read {before after : Mem 64} {writes : Address → Prop}
    (task cred signal : Address) (same : EqualOutside writes before after)
    (apart : ∀ cell ∈ locations task cred signal, ∀ i < cell.2, ¬writes (cell.1 + .ofNat 64 i))
    (base : Base) (off width : Nat) (member : (base, off, width) ∈ offsets) :
    before.loadInt (base.address task cred signal + .ofNat 64 off) width =
      after.loadInt (base.address task cred signal + .ofNat 64 off) width :=
  same.loadInt _ _ (separated task cred signal apart base off width member)

theorem Fields.frame {before after task cred signal filters t writes}
    (same : EqualOutside writes before after)
    (apart : ∀ cell ∈ locations task cred signal, ∀ i < cell.2, ¬writes (cell.1 + .ofNat 64 i))
    (represented : Fields before task cred signal filters t) : Fields after task cred signal filters t := by
  refine {blocked := ?_, pending := ?_, inEventfd := ?_, isKthread := ?_, noNewPrivs := ?_, sigpending := ?_, credential := ?_, capSysAdmin := ?_, signalPointer := ?_, rlimitNofile := ?_, seccompMode := ?_, seccompCount := ?_, seccompFilter := ?_}
  · exact (read task cred signal same apart .task TaskLayouts.task_blocked 8 (by decide)).symm.trans represented.blocked
  · exact (read task cred signal same apart .task TaskLayouts.task_pending_signal 8 (by decide)).symm.trans represented.pending
  · exact Flag.frame same (separated task cred signal apart .task TaskLayouts.task_in_eventfd 4 (by decide)) represented.inEventfd
  · exact Flag.frame same (separated task cred signal apart .task TaskLayouts.task_flags 4 (by decide)) represented.isKthread
  · exact Flag.frame same (separated task cred signal apart .task TaskLayouts.task_atomic_flags 8 (by decide)) represented.noNewPrivs
  · exact Flag.frame same (separated task cred signal apart .task TaskLayouts.task_thread_info_flags 8 (by decide)) represented.sigpending
  · exact (read task cred signal same apart .task TaskLayouts.task_cred 8 (by decide)).symm.trans represented.credential
  · exact Flag.frame same (separated task cred signal apart .cred TaskLayouts.cred_cap_effective 8 (by decide)) represented.capSysAdmin
  · exact (read task cred signal same apart .task TaskLayouts.task_signal 8 (by decide)).symm.trans represented.signalPointer
  · exact (read task cred signal same apart .signal (TaskLayouts.signal_rlim + 7 * TaskLayouts.rlimitSize + TaskLayouts.rlimit_rlim_cur) 8 (by decide)).symm.trans represented.rlimitNofile
  · exact (read task cred signal same apart .task TaskLayouts.task_seccomp_mode 4 (by decide)).symm.trans represented.seccompMode
  · exact (read task cred signal same apart .task TaskLayouts.task_seccomp_filter_count 4 (by decide)).symm.trans represented.seccompCount
  · exact (read task cred signal same apart .task TaskLayouts.task_seccomp_filter 8 (by decide)).symm.trans represented.seccompFilter

#print axioms Flag.functional
#print axioms Flag.frame
#print axioms Fields.frame
end Binary.TaskHeap
