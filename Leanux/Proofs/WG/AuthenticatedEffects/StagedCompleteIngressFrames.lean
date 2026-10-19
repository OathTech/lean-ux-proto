import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeLookup

/-! Ingress allocates RX cells without allocating TX obligations. The packet
bound is transported by the native allocator contract; queue admission and
metadata changes retain the exact staged and allocated ownership projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem new_rx_retained (pkt : RxPacket) : SameView CompletePollNative.retained (newRxSkb pkt) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases device : w.dev with
  | none => simp [newRxSkb,liftSkb_run,device] at run
  | some d =>
    rw [Packets.newRxSkb_run w a d pkt device] at run
    cases run
    unfold CompletePollNative.retained
    apply Prod.ext
    · simp [Packets.epoch,Packets.update,device]
    apply Prod.ext
    · funext pid; simp [Staged.stagedAt,Packets.update,device]
    apply Prod.ext
    · funext id; simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,device]
    apply Prod.ext
    · funext id; simp [TxDisposition.txPackets,Packets.update,device]
    · funext pid; simp [txQueueContents,handoffTxView,Packets.update,device]

theorem new_rx_entry (pkt : RxPacket) : Preserves (Inv h ledger debts locals) (newRxSkb pkt) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have kept := (ProjectedAction.iff_run_ambient _ _ _).mp (new_rx_retained pkt) w a result v b run
  obtain ⟨bounded,_⟩ := (Action.iff_run_ambient _ _ _).mp
    (Packets.newRxSkb_contract pkt) w a result v b before.packets run
  have core := before.core.quiet_views [] (by simp)
    (congrArg Prod.fst kept) (congrArg (fun x => x.2.1) kept) (congrArg (fun x => x.2.2.1) kept)
  simp only [List.append_nil] at core
  exact ⟨core,before.justified,before.allocationLinks,before.noSelected,bounded,
    before.coverage.cells (congrArg (fun x => x.2.2.2.1) kept) (congrArg (fun x => x.2.2.2.2) kept),
    before.inventory.queueContents (congrArg (fun x => x.2.2.2.2) kept) (congrArg (fun x => x.2.2.2.1) kept)⟩

theorem key_get (kid : Option KeypairId) : SameView StagedEntry.view (keypairGet kid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' entry_key_step initial

theorem next_cpu_from (last : Int) : SameView StagedEntry.view (cpumaskNextOnlineFrom last) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold cpumaskNextOnlineFrom
  simp only [branch]
  repeat' entry_key_step initial

theorem next_cpu : SameView StagedEntry.view cpumaskNextOnline := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold cpumaskNextOnline
  simp only [branch]
  repeat' entry_key_step initial

theorem enqueue (skb : SkbId) : SameView StagedEntry.view (enqueuePerDeviceAndPeerRx skb) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (CompleteDecrypt.set_rx _ _ initial)
  intro ignored
  apply preserves_bind (CompletePollNative.get_rx _ initial)
  intro pkt
  apply hoare_bind _ _ (SavedFrames.read pkt.peer (· = initial))
  intro p
  unfold branch
  apply hoare_bind _ _ (hoare_liftAmbient _ _)
  intro full
  split
  · exact hoare_consequence (preserves_pure _) (fun _ before => before.1) (fun _ _ before => before)
  · apply hoare_bind _ _ (SavedFrames.write_saved pkt.peer p {p with rxQueue := p.rxQueue.enqueue skb} (· = initial) ⟨rfl,rfl,rfl⟩)
    intro ignored
    apply hoare_consequence (P := fun w => StagedEntry.view w = initial)
      (Q := fun _ w => StagedEntry.view w = initial) ?_ (fun _ before => before.1) (fun _ _ before => before)
    change Preserves (fun w => StagedEntry.view w = initial) _
    repeat' first
      | (rx_retention_head cpumaskNextOnlineFrom; exact next_cpu_from _ initial)
      | (rx_retention_head queueDeviceWork; unfold queueDeviceWork; exact hoare_liftAmbient _ _)
      | entry_key_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
