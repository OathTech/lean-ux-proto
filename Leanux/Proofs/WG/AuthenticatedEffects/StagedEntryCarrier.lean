import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceFront
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectedClosure
import Leanux.Proofs.WG.RetirementSecurity.TxCoverage
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceWorker

/-! The entry carrier adds the meaning and native ownership missing from Core.
It is used only between staging invocations: selected tickets require an
explicit active frontier instead. Locals are actual unpublished or selected
TX batches, not an arbitrary set of resident packet cells. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance Staged

structure Inv (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (w : WGWorld) : Prop where
  core : Core history ledger debts w
  justified : Justified history ledger
  allocationLinks : AllocationLinks history ledger
  noSelected : NoSelected ledger
  packets : Packets.Inv w
  coverage : TxCoverage locals w
  inventory : TxInventory locals w

/-- The complete entry bundle holds at the actual native empty initialization.
No conservation, reachability or ownership premise is supplied by the caller. -/
theorem initial (net bare : Bool) : Inv [] [] [] [] (Runner.initialWG net bare) := by
  refine ⟨core_initial net bare,Justified.empty [],?_,no_selected_empty,?_,
    initial_tx_coverage net bare,initial_tx_inventory net bare⟩
  · intro _ _ _ member
    cases member
  · cases net <;> cases bare <;>
      simp [Packets.Inv,Packets.snapshot,Packets.deviceStore,Runner.initialWG,Bounded]
    intro i stamp impossible
    cases i <;> cases impossible

/-- Passive transport uses exact physical views and an explicitly birth-free
history suffix. The ledger and every terminal occurrence stay unchanged. -/
theorem Inv.views (before : Inv history ledger debts locals w) (suffix : List Event)
    (quiet : ∀ event ∈ suffix, birthPackets event = [])
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w)
    (material : PacketMaterial.view v = PacketMaterial.view w)
    (snapshot : Packets.snapshot v = Packets.snapshot w)
    (packets : TxDisposition.txPackets v = TxDisposition.txPackets w)
    (owners : txQueueContents v = txQueueContents w) : Inv (history ++ suffix) ledger debts locals v := by
  refine ⟨before.core.quiet_views suffix quiet epoch queues material,
    before.justified.append suffix,before.allocationLinks.append suffix,before.noSelected,?_,
    before.coverage.cells packets owners,before.inventory.queueContents owners packets⟩
  simpa only [Packets.Inv,snapshot] using before.packets

/-- Native passive actions are framed over the state fields this bundle
actually uses; unrelated counters and ambient state may change. -/
def view (w : WGWorld) :=
  (Packets.epoch w,stagedAt w,PacketMaterial.view w,Packets.snapshot w,
    TxDisposition.txPackets w,txQueueContents w)

theorem Inv.same_view (before : Inv history ledger debts locals w)
    (same : view v = view w) : Inv history ledger debts locals v := by
  have result := before.views [] (by simp) (congrArg Prod.fst same)
    (congrArg (fun x => x.2.1) same) (congrArg (fun x => x.2.2.1) same)
    (congrArg (fun x => x.2.2.2.1) same) (congrArg (fun x => x.2.2.2.2.1) same)
    (congrArg (fun x => x.2.2.2.2.2) same)
  simpa only [List.append_nil] using result

theorem native {action : WG.M α} (frame : SameView view action) :
    Preserves (Inv history ledger debts locals) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
