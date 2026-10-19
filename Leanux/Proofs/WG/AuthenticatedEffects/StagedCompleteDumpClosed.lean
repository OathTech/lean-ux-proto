import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Whole dump callbacks pair the same-ledger source proof with the allocation
invariant of the exact same native run. No cursor-release premise remains. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal NestedPeerRelease

theorem done (ctx : DumpCtx) : CompleteProduct.StateChecked (dumpDoneWith (Driver.nestedOps hooks) ctx) :=
  CompleteProduct.pair (dump_done CompleteProduct.Safe CompleteProduct.account_safe ctx)
    (by simpa only [NetlinkDumpCall.original,dumpDone_native] using dumpDone_erases ops_erases ctx)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.done ctx))
      (NetlinkDumpCall.allocation (.done ctx)))

theorem chunk (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) : CompleteProduct.StateChecked (dumpChunkWith (Driver.nestedOps hooks) ctx seq skb) :=
  CompleteProduct.pair (dump_chunk CompleteProduct.Safe CompleteProduct.account_safe ctx seq skb)
    (by simpa only [NetlinkDumpCall.original,dumpChunk_native] using dumpChunk_erases ops_erases ctx seq skb)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.chunk ctx seq skb))
      (NetlinkDumpCall.allocation (.chunk ctx seq skb)))

theorem socket (fd : Nat) : CompleteProduct.StateChecked (dumpSocketWith (Driver.nestedOps hooks) fd) :=
  CompleteProduct.pair (dump_socket CompleteProduct.Safe CompleteProduct.account_safe fd)
    (by simpa only [NetlinkDumpCall.original,dumpSocket_native] using dumpSocket_erases ops_erases fd)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.dump fd))
      (NetlinkDumpCall.allocation (.dump fd)))

theorem start (fd : Nat) (ref : DeviceRef) : CompleteProduct.StateChecked (dumpStartWith (Driver.nestedOps hooks) fd ref) :=
  CompleteProduct.pair (dump_start CompleteProduct.Safe CompleteProduct.account_safe fd ref)
    (by simpa only [NetlinkDumpCall.original,dumpStart_native] using dumpStart_erases ops_erases fd ref)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.start fd ref))
      (NetlinkDumpCall.allocation (.start fd ref)))

theorem receive (fd : Nat) : CompleteProduct.StateChecked (dumpReceiveWith (Driver.nestedOps hooks) fd) :=
  CompleteProduct.pair (dump_receive CompleteProduct.Safe CompleteProduct.account_safe fd)
    (by simpa only [NetlinkDumpCall.original,dumpReceive_native] using dumpReceive_erases ops_erases fd)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.receive fd))
      (NetlinkDumpCall.allocation (.receive fd)))

theorem device (ref : DeviceRef) : CompleteProduct.StateChecked (dumpDeviceWith (Driver.nestedOps hooks) ref) :=
  CompleteProduct.pair (dump_device CompleteProduct.Safe CompleteProduct.account_safe ref)
    (by simpa only [NetlinkDumpCall.original,dumpDevice_native] using dumpDevice_erases ops_erases ref)
    (AllocatedFrames.observed (NetlinkDumpCall.erases (.device ref))
      (NetlinkDumpCall.allocation (.device ref)))


theorem native (action : WG.M α) (same : SameDump action) :
    CompleteProduct.StateChecked (liftWGPrefix action) :=
  CompleteProduct.pair
    (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe action (frame same))
    (erasesStatePrefix_lift action)
    (AllocatedFrames.observed (erasesStatePrefix_lift action)
      (dumpLift_preserves_native allocationAmbient allocationDumpStable action same))


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
