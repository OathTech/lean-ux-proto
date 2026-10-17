import Leanux.Proofs.WG.Queues.SyscallSelection
import Leanux.Proofs.WG.Queues.AdmissionRelease

/-! The complete actual syscall derives both its funded source certificate
and its completed-poll release certificates. Selection is over that same
source certificate, including descriptor and return-to-user continuations. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SyscallFate
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem selected (call : Syscall) (index : Nat)
    (source : (ConservationSyscall.rule call).relation cs w h result v k next)
    (polls : PollReleaseCaller.Certificates h k)
    (chosen : SyscallSelection.syscall call index source c) :
    AdmissionRelease.Fate c next h k :=
  AdmissionRelease.classify (SyscallSelection.syscall_fates call index source chosen) polls

/-- Normal errno returns are retained. Input funding and owner validity are
explicit; neither the final ledger nor the poll input invariant is assumed. -/
theorem normal (call : Syscall) (entry : HolderEntry.Inv cs [] h w)
    (run : runPrefix (RxHistory.syscall call) w h=(.ok (result,v),k)) :
    ∃next,∃source : (ConservationSyscall.rule call).relation cs w h result v k next,
      HolderEntry.Inv next [] k v ∧
      ∀index c,SyscallSelection.syscall call index source c→AdmissionRelease.Fate c next h k := by
  obtain ⟨next,source,final⟩ := ConservationSyscall.normal call entry run
  have polls := (PollReleaseCaller.normal _ (PollReleaseCaller.syscall call) entry.2 run).2
  exact ⟨next,source,final,fun index c chosen=>selected call index source polls chosen⟩

end Leanux.Proofs.WG.Queues.RxCredits.SyscallFate
