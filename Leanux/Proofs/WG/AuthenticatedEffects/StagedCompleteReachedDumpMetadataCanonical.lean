import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutingCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveMetadataCanonical

/-! Dump serialization retains its original read-only walk and cancellation
branches. Cursor reference changes use the existing saved-peer source tree. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues NetlinkDump

macro "dump_metadata_step" : tactic => `(tactic| first
  | (metadata_source_head ite; apply conditionalShape)
  | (metadata_source_head Bind.bind; apply Shape.bind)
  | (metadata_source_head Pure.pure; exact .access (.pure _))
  | (metadata_source_head branch; exact .access (.ambient _))
  | (metadata_source_head getPeer; exact .access (readShape _))
  | (metadata_source_head ForIn.forIn; apply listShape)
  | (metadata_source_head liftM; exact Routing.aipShape _)
  | (metadata_source_head liftAip; exact Routing.aipShape _)
  | (metadata_source_head requireNotPending; exact .access (.pure ()))
  | metadata_source_step)

noncomputable def dumpAllowedShape (skb : NlSkb) (family masked cidr : Nat) :
    Shape (getAllowedips skb family masked cidr) := by
  unfold getAllowedips
  repeat' dump_metadata_step

noncomputable def dumpAllowedTailShape (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Lean.Json)) (node : Option NodeId) :
    Shape (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node) := by
  unfold getPeerDumpAllowedSource
  repeat' first
    | (metadata_source_head getAllowedips; exact dumpAllowedShape _ _ _ _)
    | dump_metadata_step

noncomputable def dumpPeerTailShape (p : Peer) (ctx : DumpCtx) (skb : NlSkb) :
    Shape (getPeerDumpTailSource p ctx skb) := by
  unfold getPeerDumpTailSource
  repeat' first
    | (metadata_source_head getPeerDumpAllowedSource; exact dumpAllowedTailShape _ _ _ _ _ _ _)
    | dump_metadata_step

noncomputable def dumpPeerShape (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    Shape (getPeerDump pid ctx skb) := by
  rw [getPeerDump_source]
  exact .bind (.access (readShape pid)) (fun p => dumpPeerTailShape p ctx skb)

noncomputable def dumpWalkShape (d : Device) (ctx : DumpCtx) (skb : NlSkb) :
    Shape (RxCredits.DumpReservation.walkSource d ctx skb) := by
  unfold RxCredits.DumpReservation.walkSource
  repeat' first
    | (metadata_source_head getPeerDump; exact dumpPeerShape _ _ _)
    | dump_metadata_step

noncomputable def dumpHeaderShape (d : Device) (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Shape (deviceDumpHeaderSource d ctx seq skb) := by
  unfold deviceDumpHeaderSource
  repeat' dump_metadata_step

noncomputable def dumpSocketReadShape (fd : Nat) : Shape (getNlSock fd) := by
  unfold getNlSock
  repeat' dump_metadata_step

noncomputable def dumpSocketWriteShape (fd : Nat) (sock : NlSock) : Shape (setNlSock fd sock) := by
  unfold setNlSock
  apply Shape.access
  apply Access.Shape.write
  apply KeyFrames.world
  intro w
  split <;> rfl

noncomputable def dumpCoalesceShape (messages : List NlMessage) : Shape (coalesce messages) := by
  unfold coalesce
  repeat' dump_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
