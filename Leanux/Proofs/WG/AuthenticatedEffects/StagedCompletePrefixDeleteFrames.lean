import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteSyscall
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductSource

/-! Native deletion wrappers retain the actual stronger entry and every
prior logical prefix; no native companion is reconstructed from a journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

abbrev NativeEntry := CompleteRunner.DeleteFrames.Entry
abbrev Keeps (body : PrefixM Event α) :=
  Ensures NativeEntry CompleteProduct.Safe body (fun _=>NativeEntry)
abbrev Checked (body : PrefixM Event α) :=
  Ensures NativeEntry CompleteProduct.Safe body (fun _=>CompleteProduct.Carrier)

theorem weaken (before : Keeps body) : Checked body :=
  before.consequence (fun _ _ before=>before) (fun _ _ _ after=>after.1)

theorem fs (body : FS.M α) : Keeps (liftPrefix (liftFS body)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.fs body) (fun _ _=>rfl)

theorem seccomp (body : Seccomp.M α) : Keeps (liftPrefix (liftSeccomp body)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.seccomp body) (fun _ _=>rfl)

theorem ambient (body : AmbientM α) : Keeps (liftPrefix (liftAmbient body)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.ambient body) (fun _ _=>rfl)

theorem read  : Keeps (liftPrefix (get : Leanux.M World)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.read ) (fun _ _=>rfl)

theorem read_files  : Keeps (liftPrefix (getFiles : Leanux.M FilesStruct)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.read_files ) (fun _ _=>rfl)

theorem read_task (t : TaskRef) : Keeps (liftPrefix (getTask t : Leanux.M Task)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.read_task t) (fun _ _=>rfl)

theorem modify_files (f : FilesStruct → FilesStruct) : Keeps (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.modify_files f) (fun _ _=>rfl)

theorem edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg=wgStoreView w.wg) :
    Keeps (liftPrefix (_root_.modify f : Leanux.M Unit)) :=
  Ensures.quiet (CompleteRunner.DeleteFrames.edit f same) (fun _ _=>rfl)

theorem routing_read : Product.Checked (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
  Product.native _ CompleteRunner.DeleteFrames.routing_read

theorem current_read : Keeps (liftPrefix (getCurrent : Leanux.M Task)) :=
  fs (StateT.lift TaskM.getCurrent)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
