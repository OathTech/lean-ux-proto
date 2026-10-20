import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDumpSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProduct

/-! Concrete dump source-prefix proofs and allocation endpoints refer to
one original execution. Cursor repayments use the actual disposal sources. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Dump
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal NestedPeerRelease

theorem done (ctx : DumpCtx) : Product.StateChecked (dumpDoneWith (Driver.nestedOps hooks) ctx) :=
  Product.pair (dump_done CompleteProduct.Safe CompleteProduct.account_safe ctx)
    (CompleteDump.done ctx)

theorem chunk (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) : Product.StateChecked (dumpChunkWith (Driver.nestedOps hooks) ctx seq skb) :=
  Product.pair (dump_chunk CompleteProduct.Safe CompleteProduct.account_safe ctx seq skb)
    (CompleteDump.chunk ctx seq skb)

theorem socket (fd : Nat) : Product.StateChecked (dumpSocketWith (Driver.nestedOps hooks) fd) :=
  Product.pair (dump_socket CompleteProduct.Safe CompleteProduct.account_safe fd)
    (CompleteDump.socket fd)

theorem start (fd : Nat) (ref : DeviceRef) : Product.StateChecked (dumpStartWith (Driver.nestedOps hooks) fd ref) :=
  Product.pair (dump_start CompleteProduct.Safe CompleteProduct.account_safe fd ref)
    (CompleteDump.start fd ref)

theorem receive (fd : Nat) : Product.StateChecked (dumpReceiveWith (Driver.nestedOps hooks) fd) :=
  Product.pair (dump_receive CompleteProduct.Safe CompleteProduct.account_safe fd)
    (CompleteDump.receive fd)

theorem device (ref : DeviceRef) : Product.StateChecked (dumpDeviceWith (Driver.nestedOps hooks) ref) :=
  Product.pair (dump_device CompleteProduct.Safe CompleteProduct.account_safe ref)
    (CompleteDump.device ref)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Dump
