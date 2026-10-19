import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTimerQueue

/-! Logical-prefix extension of the original source contract.
Native silent-interval correspondence remains separate.

 Native handshake consumers transport entry and terminal converse on the
same successor ledger. Nested repayments retain their actual counted receipt;
no consumer is classified as terminal-quiet merely by its result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Consumers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive NestedPeerRelease
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

abbrev nested := NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?

macro "prefix_consumer_source " safe:term " using " entry:term : tactic => `(tactic| first
  | (entry_consumer_update_head
     apply Passive.update_bind $safe $entry
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored
     change StateEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
  | (maintenance_head liftWGPrefix; apply Passive.native $safe $entry; solve | entry_consumer_native)
  | (maintenance_head HandshakeSecurity.StagedDisposal.Decoration.release; exact Disposal.original _ $safe $entry)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem initiation_check (msg : Key) : Checked debts locals Safe (initiationCheckWith nested msg) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold initiationCheckWith initiationTailWith initiationOutWith
  simp only [nested,observedOps]
  repeat' prefix_consumer_source Safe using accountSafe

theorem response_check (msg : Key) : Checked debts locals Safe (responseCheckWith nested msg) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold responseCheckWith responseTailWith
  simp only [nested,observedOps]
  repeat' prefix_consumer_source Safe using accountSafe

theorem cookie (msg : Key) : Checked debts locals Safe (cookieWith nested msg) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold cookieWith cookieAfterWith
  simp only [nested,observedOps]
  repeat' prefix_consumer_source Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Consumers
