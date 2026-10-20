import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpFrames

/-! Actual dump callbacks keep both directions of ticket accounting on one
ledger. Cursor releases retain their counted source receipts, including Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal NetlinkDump Driver NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

macro "complete_dump_step " safe:term " using " accounted:term : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix
     apply CompletePassive.native $safe $accounted
     solve | complete_dump_frame)
  | (maintenance_head ForIn.forIn; apply CompleteSendDrain.list $safe $accounted)
  | complete_handshake_step $safe using $accounted)

theorem dump_done (ctx : DumpCtx) :
    CompletePassive.Checked debts locals Safe (dumpDoneWith (nestedOps hooks) ctx) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpDoneWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | complete_dump_step Safe using accountSafe

theorem dump_replace (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    CompletePassive.Checked debts locals Safe (dumpReplaceWith (nestedOps hooks) ctx nextCursor done) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpReplaceWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | complete_dump_step Safe using accountSafe

theorem dump_finish (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    CompletePassive.Checked debts locals Safe (dumpFinishWith (nestedOps hooks) seq ctx nextCursor skb flags attrs done peers) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpFinishWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpReplaceWith; exact dump_replace Safe accountSafe _ _ _)
    | complete_dump_step Safe using accountSafe

theorem dump_tail (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    CompletePassive.Checked debts locals Safe (dumpTailWith (nestedOps hooks) d ctx skb flags attrs) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpTailWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpFinishWith; exact dump_finish Safe accountSafe _ _ _ _ _ _ _ _)
    | complete_dump_step Safe using accountSafe

theorem dump_chunk (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    CompletePassive.Checked debts locals Safe (dumpChunkWith (nestedOps hooks) ctx seq skb) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpChunkWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpTailWith; exact dump_tail Safe accountSafe _ _ _ _ _)
    | complete_dump_step Safe using accountSafe

theorem dump_socket (fd : Nat) :
    CompletePassive.Checked debts locals Safe (dumpSocketWith (nestedOps hooks) fd) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpSocketWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpChunkWith; exact dump_chunk Safe accountSafe _ _ _)
    | (maintenance_head dumpDoneWith; exact dump_done Safe accountSafe _)
    | complete_dump_step Safe using accountSafe

theorem dump_start (fd : Nat) (ref : DeviceRef) :
    CompletePassive.Checked debts locals Safe (dumpStartWith (nestedOps hooks) fd ref) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpStartWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpSocketWith; exact dump_socket Safe accountSafe _)
    | complete_dump_step Safe using accountSafe

theorem dump_receive (fd : Nat) :
    CompletePassive.Checked debts locals Safe (dumpReceiveWith (nestedOps hooks) fd) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpReceiveWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpSocketWith; exact dump_socket Safe accountSafe _)
    | complete_dump_step Safe using accountSafe

theorem dump_device (ref : DeviceRef) :
    CompletePassive.Checked debts locals Safe (dumpDeviceWith (nestedOps hooks) ref) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold dumpDeviceWith
  simp only [nestedOps,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ Safe accountSafe)
    | (maintenance_head dumpStartWith; exact dump_start Safe accountSafe _ _)
    | (maintenance_head dumpReceiveWith; exact dump_receive Safe accountSafe _)
    | complete_dump_step Safe using accountSafe


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
