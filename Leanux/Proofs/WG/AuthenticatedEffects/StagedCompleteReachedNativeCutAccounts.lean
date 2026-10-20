import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeAllocationAccounts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeTrimAccounts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeFrontier

/-! One semantic account covers ordinary states and the two native progress
families. Trim evidence names the actual loop and exact removed prefix; a new
allocation cell is an alias of an existing selected ticket, never a new birth.
Receipt-only intervals use the separate original-record completion relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal
open Transmit.Front.Residual

inductive CutStatus : History → Ledger → List TxLocalBatch → WGWorld → Ticket → Status → Prop where
  | ordinary (evidence : StatusEvidence h ledger locals v ticket status) : CutStatus h ledger locals v ticket status
  | trimLoop (cut : TrimCut h ledger debts locals pid w a n v b)
      (evidence : TrimStatusEvidence h ledger locals pid n w v ticket status) : CutStatus h ledger locals v ticket status
  | trimDrop (cut : TrimCut h ledger debts locals pid w a n v b)
      (device : v.dev=some d) (resident : d.peers[pid]?=some p) (excess : p.staged.length>MAX_STAGED_PACKETS)
      (evidence : TrimStatusEvidence h ledger locals pid (n+1) w (droppedWorld pid p d v) ticket status) :
      CutStatus h ledger locals (droppedWorld pid p d v) ticket status

inductive CellEvidence : History → Ledger → List CleanupDebt → WGWorld → SkbId → DataPacket → Prop where
  | recorded {id : SkbId} (time : Packets.epoch v=some generation) (origin : Origin h position ordinal generation id material)
      (tracked : Tracked ledger debts ticket position ordinal)
      (unique : ∀other otherGeneration otherPosition otherOrdinal otherMaterial,
        Packets.epoch v=some otherGeneration→Origin h otherPosition otherOrdinal otherGeneration id otherMaterial→
        Tracked ledger debts other otherPosition otherOrdinal→other=ticket) :
      CellEvidence h ledger debts v id material
  | allocating {id : SkbId} (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v)
      (alias : Allocation.Alias h ledger generation pid peer.internalId position packets n items v id material) :
      CellEvidence h ledger debts v id material

structure CutAccount (h : History) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (v : WGWorld) : Prop where
  valid : Valid (births h) ledger
  complete : StagedTerminalComplete.Complete h ledger
  native : NativeReady.Inv locals v
  statuses : ∀ticket status,(ticket,status)∈ledger→CutStatus h ledger locals v ticket status
  cells : ∀id material,PacketMaterial.view v id=some material→CellEvidence h ledger debts v id material

theorem CutAccount.of_current (current : Current h ledger debts locals v) : CutAccount h ledger debts locals v := by
  refine ⟨current.core.valid,current.complete,current.native,fun _ _ member=>.ordinary (current.statuses _ _ member),?_⟩
  intro id material cell
  obtain ⟨_,ticket,generation,position,ordinal,time,origin,tracked,unique⟩:=current.cell cell
  exact .recorded time origin tracked unique

theorem CutAccount.of_allocation
    (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v) :
    CutAccount h ledger debts (⟨.unpublished,pid,items⟩::locals) v := by
  refine ⟨cut.entry.core.valid,cut.entry.complete,cut.native,
    fun _ _ member=>.ordinary (allocation_status cut member),?_⟩
  intro id material cell
  rcases cut.covered cell with ⟨epoch,ticket,batch,ordinal,time,origin,tracked⟩|alias
  · refine .recorded time origin tracked ?_
    intro other otherGeneration otherPosition otherOrdinal otherMaterial otherTime otherOrigin otherTracked
    have equal : otherGeneration=epoch:=Option.some.inj (otherTime.symm.trans time)
    subst otherGeneration
    exact cut.entry.core.physical.mixed other otherPosition otherOrdinal otherTracked
      ticket batch ordinal tracked epoch id otherMaterial material otherOrigin origin
  · exact .allocating cut alias

private theorem recorded_cell (physical : Staged.Obligations.Physical h ledger debts v)
    {id : SkbId} (cell : PacketMaterial.view v id=some material) : CellEvidence h ledger debts v id material := by
  obtain ⟨ticket,generation,position,ordinal,time,origin,tracked,unique⟩:=
    physical.covered.unique_ticket physical.mixed cell
  exact .recorded time origin tracked unique

theorem CutAccount.of_trim (cut : TrimCut h ledger debts locals pid w a n v b) : CutAccount h ledger debts locals v := by
  obtain ⟨d,p,device,resident⟩:=cut.read
  have account:=cut.packet_account
  exact ⟨cut.entry.entry.core.valid,cut.entry.complete,account.1,
    fun _ _ member=>.trimLoop cut (trim_status cut.entry account.2 account.1
      (cut.path.staged_packets device resident) member),fun _ _ cell=>recorded_cell account.2 cell⟩

theorem CutAccount.of_trim_drop (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p) (excess : p.staged.length>MAX_STAGED_PACKETS) :
    CutAccount h ledger debts locals (droppedWorld pid p d v) := by
  have account:=cut.dropped_packet_account device resident
  exact ⟨cut.entry.entry.core.valid,cut.entry.complete,account.1,
    fun _ _ member=>.trimDrop cut device resident excess (trim_status cut.entry account.2 account.1
      (cut.dropped_staged_packets device resident excess) member),fun _ _ cell=>recorded_cell account.2 cell⟩

def Account (h : History) (v : WGWorld) : Prop := ∃ledger debts locals,CutAccount h ledger debts locals v

theorem Stable.account (current : Stable h v) : Account h v := by
  obtain ⟨ledger,debts,locals,account⟩:=current
  exact ⟨ledger,debts,locals,.of_current account⟩

theorem Transient.account (cut : Transient h v) : Account h v := by
  cases cut with
  | allocating interval=>exact ⟨_,_,_,.of_allocation interval⟩
  | trimLoop interval=>exact ⟨_,_,_,.of_trim interval⟩
  | trimDrop interval device resident excess=>exact ⟨_,_,_,.of_trim_drop interval device resident excess⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
