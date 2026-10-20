import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeAllocationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeCurrent

/-! Every partial-allocation ticket retains its actual current status. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal

theorem allocation_status
    (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v)
    (member : (ticket,status)∈ledger) :
    StatusEvidence h ledger (⟨.unpublished,pid,items⟩::locals) v ticket status := by
  cases status with
  | terminal outcome=>exact cut.entry.justified ticket outcome member
  | pending location=>
      cases location with
      | staged epoch owner stamp=>
          obtain ⟨d,device⟩:=cut.device
          exact ⟨(cut.entry.core.queues.views (cut.path.epoch device) cut.path.staged) epoch owner stamp,
            mem_pendingAt.mpr member⟩
      | allocated batch ordinal=>
          obtain ⟨epoch,id,material,origin,atEpoch,cell⟩:=cut.old_backing.1 ticket batch ordinal member
          obtain ⟨packet,resident,_⟩:=Option.map_eq_some_iff.mp cell
          exact ⟨epoch,id,material,(cut.entry.links ticket batch ordinal member).at_origin origin,
            atEpoch,cell,cut.native.2.1 id packet resident⟩
      | selected other=>
          have evidence:=selected_status cut.entry member
          obtain ⟨r,epoch,owner,saved,recorded,native,pidEq,chosen,time,vacant,aligned,pending⟩:=evidence
          obtain ⟨d,device⟩:=cut.device
          exact ⟨r,epoch,owner,saved,recorded,native,pidEq,chosen,
            (cut.path.epoch device).trans time,congrFun cut.path.staged owner |>.trans vacant,aligned,pending⟩

/-- Security: a partially allocated batch leaves every original admission
with one current status. New cells are aliases of those selected obligations,
not additional tickets, and prior terminals remain tied to their receipts. -/
theorem allocation_partition
    (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v)
    (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧
      StatusEvidence h ledger (⟨.unpublished,pid,items⟩::locals) v ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=cut.entry.core.total_partition born
  exact ⟨status,member,allocation_status cut member,unique⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
