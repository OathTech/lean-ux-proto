import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpErasure
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObservedFrames

/-! Complete dump callers observe actual cursor disposals. Native execution,
old journals and stopped prefixes agree without a nonfinal-release premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

/-- The original wgGetDeviceDone execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpDone_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (ctx : DumpCtx) :
    StateProjectsPrefix ρ id (dumpDoneWith (observedOps release decode) ctx)
      (liftWGPrefix (wgGetDeviceDone ctx)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpDone_frame ρ (observedOps_frames release decode ρ quiet) ctx)
  simpa only [dumpDone_native] using
    dumpDone_erases (observedOps_erases release decode) ctx

/-- The original wgGetDeviceDump execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpChunk_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    StateProjectsPrefix ρ id (dumpChunkWith (observedOps release decode) ctx prevSeq skb)
      (liftWGPrefix (wgGetDeviceDump ctx prevSeq skb)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpChunk_frame ρ (observedOps_frames release decode ρ quiet) ctx prevSeq skb)
  simpa only [dumpChunk_native] using
    dumpChunk_erases (observedOps_erases release decode) ctx prevSeq skb

/-- The original netlinkDump execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpSocket_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (fd : Nat) :
    StateProjectsPrefix ρ id (dumpSocketWith (observedOps release decode) fd)
      (liftWGPrefix (netlinkDump fd)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpSocket_frame ρ (observedOps_frames release decode ρ quiet) fd)
  simpa only [dumpSocket_native] using
    dumpSocket_erases (observedOps_erases release decode) fd

/-- The original netlinkDumpStart execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpStart_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (fd : Nat) (ref : DeviceRef) :
    StateProjectsPrefix ρ id (dumpStartWith (observedOps release decode) fd ref)
      (liftWGPrefix (netlinkDumpStart fd ref)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpStart_frame ρ (observedOps_frames release decode ρ quiet) fd ref)
  simpa only [dumpStart_native] using
    dumpStart_erases (observedOps_erases release decode) fd ref

/-- The original netlinkRecvmsg execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpReceive_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (fd : Nat) :
    StateProjectsPrefix ρ id (dumpReceiveWith (observedOps release decode) fd)
      (liftWGPrefix (netlinkRecvmsg fd)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpReceive_frame ρ (observedOps_frames release decode ρ quiet) fd)
  simpa only [dumpReceive_native] using
    dumpReceive_erases (observedOps_erases release decode) fd

/-- The original wgGetDevice execution keeps its cursor repayment cuts;
hiding only their disposal events preserves its complete old Stop prefix. -/
theorem dumpDevice_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (ref : DeviceRef) :
    StateProjectsPrefix ρ id (dumpDeviceWith (observedOps release decode) ref)
      (liftWGPrefix (wgGetDevice ref)) := by
  apply Exchange.quiet_native_projection ρ _ _ ?_
    (dumpDevice_frame ρ (observedOps_frames release decode ρ quiet) ref)
  simpa only [dumpDevice_native] using
    dumpDevice_erases (observedOps_erases release decode) ref

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
