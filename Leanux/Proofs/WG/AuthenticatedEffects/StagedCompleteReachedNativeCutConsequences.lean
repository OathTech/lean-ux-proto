import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeCutAccounts

/-! The same semantic consequences now cover active allocation and trim,
not only stable receipt boundaries. Fixed-record completion remains explicit
and never substitutes an arbitrary later world or history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal

theorem CutStatus.terminal (evidence : CutStatus h ledger locals v ticket (.terminal outcome)) :
    StagedProvenance.Evidence h ticket outcome := by
  cases evidence with
  | ordinary evidence=>exact evidence
  | trimLoop cut evidence=>exact evidence
  | trimDrop cut device resident excess evidence=>exact evidence

/-- Security: each admitted ticket has exactly one current status. A trim
interval retains its exact removed cohort on the same ledger; partial native
allocation retains selected statuses and creates only cell aliases. -/
theorem CutAccount.partition (account : CutAccount h ledger debts locals v) (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧ CutStatus h ledger locals v ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=(Staged.Obligations.Step.refl ledger).total_partition account.valid born
  exact ⟨status,member,account.statuses ticket status member,unique⟩

theorem CutAccount.terminal_unique (account : CutAccount h ledger debts locals v)
    (first : (ticket,Status.terminal left)∈ledger) (second : (ticket,Status.terminal right)∈ledger) : left=right :=
  Status.terminal.inj (unique_status (account.valid.1.symm ▸ account.valid.2) first second)

theorem CutAccount.pending_not_terminal (account : CutAccount h ledger debts locals v)
    (pending : (ticket,Status.pending location)∈ledger) (terminal : (ticket,Status.terminal outcome)∈ledger) : False := by
  have impossible:=unique_status (account.valid.1.symm ▸ account.valid.2) pending terminal
  cases impossible

/-- Security: every resident TX cell has a native owner and either its unique
recorded allocation backing or the actual partial allocator's selected-ticket
alias. A silent native allocation is never treated as an extra admission. -/
theorem CutAccount.cell {id : SkbId} (account : CutAccount h ledger debts locals v)
    (cell : PacketMaterial.view v id=some material) :
    TxOwned locals v id ∧ CellEvidence h ledger debts v id material := by
  obtain ⟨packet,resident,_⟩:=Option.map_eq_some_iff.mp cell
  exact ⟨account.native.2.1 id packet resident,account.cells id material cell⟩

theorem CutAccount.receipt_count (account : CutAccount h ledger debts locals v)
    (recorded : h[position]?=some event)
    (requested : StagedTerminalComplete.demand position event=some request) :
    (StagedTerminalComplete.tickets request.outcome ledger).length=request.count :=
  account.complete.at recorded request requested

/-- Security: a native singleton send or drop receipt has exactly one ticket,
with its original terminal evidence, including inside allocation or trim. -/
theorem CutAccount.receipt_singleton (account : CutAccount h ledger debts locals v)
    (recorded : h[position]?=some event)
    (requested : StagedTerminalComplete.demand position event=some ⟨outcome,1⟩) :
    ∃ticket,ticket∈births h ∧ (ticket,Status.terminal outcome)∈ledger ∧
      StagedProvenance.Evidence h ticket outcome ∧
      ∀other,(other,Status.terminal outcome)∈ledger→other=ticket := by
  obtain ⟨ticket,member,unique⟩:=account.complete.singleton recorded requested
  refine ⟨ticket,?_,member,(account.statuses ticket (.terminal outcome) member).terminal,unique⟩
  rw [←account.valid.1]
  exact List.mem_map.mpr ⟨_,member,rfl⟩

def AccountOrRecords (h : History) (v : WGWorld) : Prop :=
  Account h v ∨ ∃last,RecordsDue h v last ∧ Account last v

theorem Frontier.account_or_records (frontier : Frontier h v) : AccountOrRecords h v := by
  rcases frontier with current|⟨last,due,current⟩|interval
  · exact Or.inl current.account
  · exact Or.inr ⟨last,due,current.account⟩
  · exact Or.inl interval.account

/-- Security: every declared initialized point carries a full semantic ticket
account now or after its original fixed records on the same native world.
Allocation aliases and removed trim cohorts have derived per-ticket meaning;
finer native source coverage remains a separate obligation. -/
theorem initialized_account_or_records (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    Runner.Points.Covered (children nativeConsume nativeNapi nativeWorker nativeWork nativeDispatch)
      (fun h w=>AccountOrRecords h w.wg) (Runner.Points.executeShape trace placeholders) [] := by
  intro site u middle point
  exact (initialized_frontier trace placeholders site u middle point).account_or_records

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
