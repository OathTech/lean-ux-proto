import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesFrontier

/-! Each fixed admitted ticket has one native-backed pending location or one
receipt-backed terminal. Queue aliases and post-terminal cleanup are not new
logical obligations or further terminal results. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity AllocatedObligation CausalJournal StagedProvenance StagedTerminalComplete
open HandshakeSecurity.StagedConservation

def PendingEvidence (history : List Event) (ledger : Ledger) (locals : List TxLocalBatch)
    (w : WGWorld) (ticket : Ticket) : Pending → Prop
  | .staged generation pid stamp =>
    Aligned (Born history generation pid stamp)
      (pendingAt (.staged generation pid stamp) ledger) (stagedPackets generation pid stamp w) ∧
      ticket ∈ pendingAt (.staged generation pid stamp) ledger
  | .selected position =>
    ∃ (r : Take.Receipt) (peer : Peer) (generation : Nat),
      history[position]? = some (.stagingTaken r) ∧ r.Valid ∧ r.run.value = some peer ∧
      w = r.run.after ∧
      Aligned (Born history generation r.pid peer.internalId)
        (pendingAt (.selected position) ledger) peer.staged ∧
      ticket ∈ pendingAt (.selected position) ledger
  | .allocated position ordinal =>
    ∃ generation id material, Lineage history ticket position ordinal generation id material ∧
      Packets.epoch w = some generation ∧ PacketMaterial.view w id = some material ∧ TxOwned locals w id

def StatusEvidence (history : List Event) (ledger : Ledger) (locals : List TxLocalBatch)
    (w : WGWorld) (ticket : Ticket) : Status → Prop
  | .pending location => PendingEvidence history ledger locals w ticket location
  | .terminal outcome => Evidence history ticket outcome

theorem Cut.pending (cut : Cut history ledger debts locals w)
    (member : (ticket,Status.pending location) ∈ ledger) :
    PendingEvidence history ledger locals w ticket location := by
  cases location with
  | staged generation pid stamp => exact ⟨cut.core.queues generation pid stamp,mem_pendingAt.mpr member⟩
  | selected position =>
    obtain ⟨r,peer,generation,recorded,native,chosen,same,aligned⟩ := cut.selected ticket position member
    exact ⟨r,peer,generation,recorded,native,chosen,same,aligned,mem_pendingAt.mpr member⟩
  | allocated position ordinal =>
    obtain ⟨generation,id,material,origin,epoch,cell⟩ := cut.core.physical.resident ticket position ordinal member
    obtain ⟨packet,resident,_⟩ := Option.map_eq_some_iff.mp cell
    exact ⟨generation,id,material,(cut.links ticket position ordinal member).at_origin origin,
      epoch,cell,cut.native.2.1 id packet resident⟩

theorem Cut.status {status : Status} (cut : Cut history ledger debts locals w) (member : (ticket,status) ∈ ledger) :
    StatusEvidence history ledger locals w ticket status := by
  cases status with
  | pending location => exact cut.pending member
  | terminal outcome => exact cut.justified ticket outcome member

/-- The same ledger accounts for every canonical birth, including positions
with equal packet bytes. Exactly one location or terminal is selected. -/
theorem Cut.partition (cut : Cut history ledger debts locals w) (born : ticket ∈ births history) :
    ∃ status, (ticket,status) ∈ ledger ∧ StatusEvidence history ledger locals w ticket status ∧
      ∀ other, (ticket,other) ∈ ledger → other = status := by
  obtain ⟨status,member,unique⟩ := cut.core.total_partition born
  exact ⟨status,member,cut.status member,unique⟩

theorem Cut.terminal_unique (cut : Cut history ledger debts locals w)
    (first : (ticket,Status.terminal left) ∈ ledger)
    (second : (ticket,Status.terminal right) ∈ ledger) : left = right :=
  Status.terminal.inj (unique_status (cut.core.valid.1.symm ▸ cut.core.valid.2) first second)

/-- One admitted ticket cannot account for two socket attempts, including
an error followed by a success: both position and result are identical. -/
theorem Cut.socket_unique (cut : Cut history ledger debts locals w)
    (first : (ticket,Status.terminal (.socket left success)) ∈ ledger)
    (second : (ticket,Status.terminal (.socket right otherSuccess)) ∈ ledger) :
    left = right ∧ success = otherSuccess := by
  cases cut.terminal_unique first second
  exact ⟨rfl,rfl⟩

theorem Cut.pending_not_terminal (cut : Cut history ledger debts locals w)
    (pending : (ticket,Status.pending location) ∈ ledger)
    (terminal : (ticket,Status.terminal outcome) ∈ ledger) : False := by
  have impossible := unique_status (cut.core.valid.1.symm ▸ cut.core.valid.2) pending terminal
  cases impossible

/-- A remaining native cell is assigned to exactly one ticket, either pending
or already terminal with cleanup debt. Its physical owner is retained too. -/
theorem Cut.cell {id : SkbId} (cut : Cut history ledger debts locals w)
    (cell : PacketMaterial.view w id = some material) :
    TxOwned locals w id ∧ ∃ ticket generation position ordinal,
      Packets.epoch w = some generation ∧ Origin history position ordinal generation id material ∧
      Tracked ledger debts ticket position ordinal ∧
      ∀ other otherGeneration otherPosition otherOrdinal otherMaterial,
        Packets.epoch w = some otherGeneration →
        Origin history otherPosition otherOrdinal otherGeneration id otherMaterial →
        Tracked ledger debts other otherPosition otherOrdinal → other = ticket := by
  exact ⟨(cut.core.physical.covered.owned cut.native.2.1 cell).2,
    cut.core.physical.covered.unique_ticket cut.core.physical.mixed cell⟩

/-- Stop safety yields a single ledger for the complete admission domain;
selected locals and intermediate cleanup debt remain explicit. -/
theorem forward (safe : CompleteProduct.Safe history) :
    ∃ ledger debts locals w, Cut history ledger debts locals w ∧
      ∀ ticket ∈ births history, ∃ status, (ticket,status) ∈ ledger ∧
        StatusEvidence history ledger locals w ticket status ∧
        ∀ other, (ticket,other) ∈ ledger → other = status := by
  obtain ⟨ledger,debts,locals,w,cut⟩ := safe_cut safe
  exact ⟨ledger,debts,locals,w,cut,fun _ born=>cut.partition born⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
