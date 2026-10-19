import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocation

/-! Native geometry at each fixed allocator prefix. New cells are owned by
the active unpublished continuation; old pending cells and cleanup debts
retain their exact historical backing without a fabricated batch receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations AllocatedObligation

theorem alignment_length {related : α→β→Prop}
    (aligned : Aligned related left right) : left.length=right.length := by
  induction aligned with
  | nil=>rfl
  | cons _ _ ih=>simp only [List.length_cons,ih]

theorem Path.epoch (path : Path packets w a n items v) (device : w.dev=some d) :
    Packets.epoch v=Packets.epoch w := by
  obtain ⟨_,_,last,atLast,_,same,_⟩ :=
    TxDisposition.ItemSeparation.allocate_result (packets.take n) device path.native
  simp only [Packets.epoch,device,atLast,Option.map_some,same]

theorem Path.native_ready (path : Path packets w a n items v)
    (before : NativeReady.Inv locals w) (device : w.dev=some d) (pid : PeerId) :
    NativeReady.Inv (⟨.unpublished,pid,items⟩::locals) v :=
  ⟨ReadyCarrier.allocated_bounds (packets.take n) before.1 a a path.native,
   before.2.1.allocate pid (packets.take n) a a path.native,
   before.2.2.allocate before.1 device pid (packets.take n) a a path.native⟩

theorem Path.old_resident (path : Path packets w a n items v)
    (before : Resident history ledger w) (bounded : Packets.Inv w) :
    Resident history ledger v :=
  fun ticket position ordinal member =>
    (before ticket position ordinal member).allocate bounded (packets.take n) path.native

theorem Path.old_cleanup (path : Path packets w a n items v)
    (before : DebtsResident history ledger debts w) (bounded : Packets.Inv w) :
    DebtsResident history ledger debts v := by
  intro debt member
  obtain ⟨terminal,backed⟩ := before debt member
  exact ⟨terminal,backed.allocate bounded (packets.take n) path.native⟩

theorem Path.fresh (path : Path packets w a n items v) (bounded : Packets.Inv w)
    {skb : SkbId} (resident : TxDisposition.txPackets w skb=some packet) :
    skb∉items ∧ TxDisposition.txPackets v skb=some packet :=
  TxDisposition.ItemSeparation.allocate_resident bounded resident path.native

theorem Path.distinct (path : Path packets w a n items v) (device : w.dev=some d) :
    items.Nodup := TxDisposition.ItemSeparation.allocate_nodup device path.native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
