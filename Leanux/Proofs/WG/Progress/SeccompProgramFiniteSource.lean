import Leanux.Proofs.WG.Progress.SeccompProgramSource
import Leanux.Proofs.WG.Progress.SeccompLocalFiniteSource

/-! Concrete finite callers. The native operation value replaces only alloc;
it is passed explicitly and does not install or modify an instance. Thus the
original bounded checker also uses finite .kmallocArrayMasks encounters. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompProgramFinite
open Leanux Leanux.Seccomp

def allocate (site : SAllocSite) : Seccomp.M Bool :=
  monadLift (hiddenAllocFinite site.toAllocSite)

theorem allocate_source (site : SAllocSite) :
    (Seccomp.alloc site : Seccomp.M Bool) = allocate site := by
  change (monadLift (AmbientM.hiddenAlloc site.toAllocSite) : Seccomp.M Bool) = _
  rw [hiddenAlloc_finite_source]
  rfl

abbrev allocationOps : SeccompM Seccomp.M :=
  { (inferInstance : SeccompM Seccomp.M) with alloc := allocate }

theorem allocationOps_source : allocationOps = (inferInstance : SeccompM Seccomp.M) := by
  have allocation : allocate = (fun site => (Seccomp.alloc site : Seccomp.M Bool)) := by
    funext site
    exact (allocate_source site).symm
  unfold allocationOps
  rw [allocation]

def migrate (insns orig : Seccomp.ClassicProg) : Seccomp.M (Except Int Seccomp.BpfProg) :=
  @SeccompProgram.migrateWith Seccomp.M allocationOps SeccompFinite.convert insns orig

theorem migrate_source (insns orig : Seccomp.ClassicProg) :
    (bpfMigrateFilter insns orig : Seccomp.M _) = migrate insns orig := by
  unfold migrate
  rw [allocationOps_source, SeccompProgram.migrate_source]
  have convert : (fun p n s l => (bpfConvertFilter p n s l : Seccomp.M _)) =
      SeccompFinite.convert := by
    funext p n s l
    exact SeccompFinite.convert_source p n s l
  exact congrArg (fun callback => SeccompProgram.migrateWith callback insns orig) convert

def prepare (insns orig : Seccomp.ClassicProg) : Seccomp.M (Except Int Seccomp.BpfProg) :=
  @SeccompProgram.prepareWith Seccomp.M allocationOps migrate insns orig

theorem prepare_source (insns orig : Seccomp.ClassicProg) :
    (bpfPrepareFilter insns orig : Seccomp.M _) = prepare insns orig := by
  unfold prepare
  rw [allocationOps_source, SeccompProgram.prepare_source]
  have migration : (fun p o => (bpfMigrateFilter p o : Seccomp.M _)) = migrate := by
    funext p o
    exact migrate_source p o
  exact congrArg (fun callback => SeccompProgram.prepareWith callback insns orig) migration

def create (fprog : Seccomp.SockFprog) : Seccomp.M (Except Int Seccomp.BpfProg) :=
  @SeccompProgram.createWith Seccomp.M allocationOps prepare fprog

theorem create_source (fprog : Seccomp.SockFprog) :
    (bpfProgCreateFromUser fprog : Seccomp.M _) = create fprog := by
  unfold create
  rw [allocationOps_source, SeccompProgram.create_source]
  have preparation : (fun p o => (bpfPrepareFilter p o : Seccomp.M _)) = prepare := by
    funext p o
    exact prepare_source p o
  exact congrArg (fun callback => SeccompProgram.createWith callback fprog) preparation

end Leanux.Proofs.WG.Progress.SeccompProgramFinite

namespace Leanux.Proofs.WG.Progress.SeccompLocalProgramFinite
open Leanux Leanux.Seccomp

/-- Local's original allocation callback is already a finite list/state
operation. The finite converter is the only changed callback here. -/
def migrate (insns orig : Seccomp.ClassicProg) : Local.L (Except Int Seccomp.BpfProg) :=
  SeccompProgram.migrateWith SeccompLocalFinite.convert insns orig

theorem migrate_source (insns orig : Seccomp.ClassicProg) :
    (bpfMigrateFilter insns orig : Local.L _) = migrate insns orig := by
  unfold migrate
  rw [SeccompProgram.migrate_source]
  have convert : (fun p n s l => (bpfConvertFilter p n s l : Local.L _)) =
      SeccompLocalFinite.convert := by
    funext p n s l
    exact SeccompLocalFinite.convert_source p n s l
  exact congrArg (fun callback => SeccompProgram.migrateWith callback insns orig) convert

def prepare (insns orig : Seccomp.ClassicProg) : Local.L (Except Int Seccomp.BpfProg) :=
  SeccompProgram.prepareWith migrate insns orig

theorem prepare_source (insns orig : Seccomp.ClassicProg) :
    (bpfPrepareFilter insns orig : Local.L _) = prepare insns orig := by
  unfold prepare
  rw [SeccompProgram.prepare_source]
  have migration : (fun p o => (bpfMigrateFilter p o : Local.L _)) = migrate := by
    funext p o
    exact migrate_source p o
  exact congrArg (fun callback => SeccompProgram.prepareWith callback insns orig) migration

def create (fprog : Seccomp.SockFprog) : Local.L (Except Int Seccomp.BpfProg) :=
  SeccompProgram.createWith prepare fprog

theorem create_source (fprog : Seccomp.SockFprog) :
    (bpfProgCreateFromUser fprog : Local.L _) = create fprog := by
  unfold create
  rw [SeccompProgram.create_source]
  have preparation : (fun p o => (bpfPrepareFilter p o : Local.L _)) = prepare := by
    funext p o
    exact prepare_source p o
  exact congrArg (fun callback => SeccompProgram.createWith callback fprog) preparation

end Leanux.Proofs.WG.Progress.SeccompLocalProgramFinite
