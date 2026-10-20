import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeInitialized

/-! A semantic current-state account unifies resident and held plaintext
statuses. Ownership, receipt completeness and the unique ticket partition
refer to the same ledger and actual WG projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staged.Origins RetirementSecurity AllocatedObligation

structure Current (h : History) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (w : WGWorld) : Prop where
  core : Core h ledger debts w
  complete : StagedTerminalComplete.Complete h ledger
  native : NativeReady.Inv locals w
  statuses : ∀ticket status,(ticket,status)∈ledger→StatusEvidence h ledger locals w ticket status

theorem Current.of_accounted (before : CompleteCarrier.Accounted h ledger debts locals w) :
    Current h ledger debts locals w :=
  ⟨before.entry.core,before.complete,⟨before.entry.packets,before.entry.coverage,before.entry.inventory⟩,
    fun _ _ member=>accounted_status before member⟩

theorem Current.of_selected
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Current h ledger debts locals w :=
  ⟨before.core,before.complete,before.native,fun _ _ member=>selected_status before member⟩

/-- Security: every admitted ticket has exactly one current native-backed
pending status or one receipt-backed terminal on this same ledger. -/
theorem Current.partition (current : Current h ledger debts locals w) (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧ StatusEvidence h ledger locals w ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=current.core.total_partition born
  exact ⟨status,member,current.statuses ticket status member,unique⟩

theorem Current.terminal_unique (current : Current h ledger debts locals w)
    (first : (ticket,Status.terminal left)∈ledger) (second : (ticket,Status.terminal right)∈ledger) : left=right :=
  Status.terminal.inj (unique_status (current.core.valid.1.symm ▸ current.core.valid.2) first second)

/-- Security: every resident TX cell has a native owner and one original
ticket; an already terminal cell retains its cleanup debt, not a new outcome. -/
theorem Current.cell {id : SkbId} (current : Current h ledger debts locals w)
    (cell : PacketMaterial.view w id=some material) :
    TxOwned locals w id ∧ ∃ticket generation position ordinal,
      Packets.epoch w=some generation ∧ Origin h position ordinal generation id material ∧
      Tracked ledger debts ticket position ordinal ∧
      ∀other otherGeneration otherPosition otherOrdinal otherMaterial,
        Packets.epoch w=some otherGeneration→
        Origin h otherPosition otherOrdinal otherGeneration id otherMaterial→
        Tracked ledger debts other otherPosition otherOrdinal→other=ticket :=
  ⟨(current.core.physical.covered.owned current.native.2.1 cell).2,
    current.core.physical.covered.unique_ticket current.core.physical.mixed cell⟩

/-- Security: a recorded send or disposal receipt has exactly the native
number of terminal tickets, so cleanup cannot supply a second disposition. -/
theorem Current.receipt_count (current : Current h ledger debts locals w)
    (recorded : h[position]?=some event)
    (requested : StagedTerminalComplete.demand position event=some request) :
    (StagedTerminalComplete.tickets request.outcome ledger).length=request.count :=
  current.complete.at recorded request requested

theorem Current.receipt_singleton (current : Current h ledger debts locals w)
    (recorded : h[position]?=some event)
    (requested : StagedTerminalComplete.demand position event=some ⟨outcome,1⟩) :
    ∃ticket,ticket∈births h ∧ (ticket,Status.terminal outcome)∈ledger ∧
      StagedProvenance.Evidence h ticket outcome ∧
      ∀other,(other,Status.terminal outcome)∈ledger→other=ticket := by
  obtain ⟨ticket,member,unique⟩:=current.complete.singleton recorded requested
  refine ⟨ticket,?_,member,current.statuses ticket (.terminal outcome) member,unique⟩
  rw [←current.core.valid.1]
  exact List.mem_map.mpr ⟨_,member,rfl⟩

def Stable (h : History) (w : WGWorld) : Prop :=
  ∃ledger debts locals,Current h ledger debts locals w

theorem Stable.of_accounted (before : CompleteCarrier.Accounted h ledger debts locals w) : Stable h w :=
  ⟨ledger,debts,locals,Current.of_accounted before⟩

theorem Stable.of_selected
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) : Stable h w :=
  ⟨ledger,debts,locals,Current.of_selected before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
