import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReceiveConsumer
import Leanux.Proofs.WG.Packets.Primitives

/-! RX polling may erase a receive cell, so the full packet snapshot is not
framed as equal. The existing packet bound is transported by its actual
primitive contract; every staged/TX ledger field and terminal stays fixed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompletePassive Queues.RxCredits
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def retained (w : WGWorld) :=
  (Packets.epoch w,Staged.stagedAt w,PacketMaterial.view w,
    TxDisposition.txPackets w,txQueueContents w)

theorem free_rx_retained (skb : SkbId) : SameView retained (freeRxSkb skb) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [freeRxSkb,liftSkb_run,device] at run
  | some d =>
    cases resident : d.rxSkbs[skb]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some packet =>
      rw [Packets.freeRxSkb_run w a d skb packet device resident] at run
      cases run
      unfold retained
      apply Prod.ext
      · simp [Packets.epoch,Packets.update,device]
      apply Prod.ext
      · funext pid; simp [Staged.stagedAt,Packets.update,device]
      apply Prod.ext
      · funext id; simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,device]
      apply Prod.ext
      · funext id; simp [TxDisposition.txPackets,Packets.update,device]
      · funext pid; simp [txQueueContents,handoffTxView,Packets.update,device]

theorem free_rx_entry (skb : SkbId) : Preserves (Inv h ledger debts locals) (freeRxSkb skb) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have kept := (ProjectedAction.iff_run_ambient _ _ _).mp (free_rx_retained skb) w a result v b run
  obtain ⟨bounded,_⟩ := (Action.iff_run_ambient _ _ _).mp
    (Packets.freeRxSkb_contract skb) w a result v b before.packets run
  have core := before.core.quiet_views [] (by simp)
    (congrArg Prod.fst kept) (congrArg (fun x => x.2.1) kept) (congrArg (fun x => x.2.2.1) kept)
  simp only [List.append_nil] at core
  exact ⟨core,before.justified,before.allocationLinks,before.noSelected,bounded,
    before.coverage.cells (congrArg (fun x => x.2.2.2.1) kept) (congrArg (fun x => x.2.2.2.2) kept),
    before.inventory.queueContents (congrArg (fun x => x.2.2.2.2) kept) (congrArg (fun x => x.2.2.2.1) kept)⟩

theorem free_rx (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) (skb : SkbId) :
    Checked debts locals Safe (liftWGPrefix (freeRxSkb skb)) := by
  apply StatePrefixEnsures.lift
  · intro h w _ before
    obtain ⟨ledger,accounted⟩ := before
    exact accountSafe ledger h w accounted
  · intro h w a value v b before run
    obtain ⟨ledger,entry,complete⟩ := before
    exact ⟨ledger,(hoare_iff_run_ambient _ _ _).mp (free_rx_entry skb) w a value v b entry run,complete⟩

theorem get_rx (skb : SkbId) : SameView StagedEntry.view (getRxSkb skb) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  exact congrArg StagedEntry.view (Packets.getRxSkb_current skb w v value a b run).1

theorem counter (kid : KeypairId) (nonce : Nat) : SameView StagedEntry.view (counterValidate kid nonce) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold counterValidate
  simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => StagedEntry.view w = initial)
       intro x b
       change Preserves (fun w => StagedEntry.view w = initial) _)
    | entry_key_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollNative
