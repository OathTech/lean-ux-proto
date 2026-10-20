import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesPartition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelected

/-! Packet status at the actual current WG projection. A saved plaintext
batch is backed by its original take and the current empty resident queue;
the current world need not equal the earlier take snapshot. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staged.Origins RetirementSecurity AllocatedObligation
open HandshakeSecurity.StagedConservation

def SelectedEvidence (h : List Event) (ledger : Ledger) (w : WGWorld)
    (ticket : Ticket) (position : Nat) : Prop :=
  ∃ (r : Take.Receipt) (generation : Nat) (pid : PeerId) (peer : Peer),
    h[position]?=some (.stagingTaken r) ∧ r.Valid ∧ r.pid=pid ∧ r.run.value=some peer ∧
    Packets.epoch w=some generation ∧ Staged.stagedAt w pid=some (peer.internalId,[]) ∧
    Aligned (Born h generation pid peer.internalId) (pendingAt (.selected position) ledger) peer.staged ∧
    ticket∈pendingAt (.selected position) ledger

def PendingEvidence (h : List Event) (ledger : Ledger) (locals : List TxLocalBatch)
    (w : WGWorld) (ticket : Ticket) : Pending → Prop
  | .selected position=>SelectedEvidence h ledger w ticket position
  | location=>CompleteConsequences.PendingEvidence h ledger locals w ticket location

def StatusEvidence (h : List Event) (ledger : Ledger) (locals : List TxLocalBatch)
    (w : WGWorld) (ticket : Ticket) : Status → Prop
  | .pending location=>PendingEvidence h ledger locals w ticket location
  | .terminal outcome=>StagedProvenance.Evidence h ticket outcome

theorem accounted_status (before : CompleteCarrier.Accounted h ledger debts locals w)
    (member : (ticket,status)∈ledger) : StatusEvidence h ledger locals w ticket status := by
  cases status with
  | terminal outcome=>exact before.entry.justified ticket outcome member
  | pending location=>
      cases location with
      | staged generation pid stamp=>exact (CompleteConsequences.accounted before).pending member
      | allocated position ordinal=>exact (CompleteConsequences.accounted before).pending member
      | selected position=>
          have impossible:=mem_pendingAt.mpr member
          rw [before.entry.noSelected position] at impossible
          cases impossible

theorem selected_status
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (member : (ticket,status)∈ledger) : StatusEvidence h ledger locals w ticket status := by
  cases status with
  | terminal outcome=>exact before.justified ticket outcome member
  | pending location=>
      cases location with
      | staged epoch owner stamp=>exact ⟨before.core.queues epoch owner stamp,mem_pendingAt.mpr member⟩
      | allocated batch ordinal=>
          obtain ⟨epoch,id,material,origin,atEpoch,cell⟩:=before.core.physical.resident ticket batch ordinal member
          obtain ⟨packet,resident,_⟩:=Option.map_eq_some_iff.mp cell
          exact ⟨epoch,id,material,(before.links ticket batch ordinal member).at_origin origin,
            atEpoch,cell,before.native.2.1 id packet resident⟩
      | selected other=>
          have same : other=position := by
            by_cases same : other=position
            · exact same
            · have impossible:=mem_pendingAt.mpr member
              rw [before.only other same] at impossible
              cases impossible
          subst other
          obtain ⟨past,suffix,r,historyEq,positionEq,pidEq,native,chosen,_,_,_,_⟩:=before.anchor.reached
          have recorded : h[position]?=some (.stagingTaken r) := by
            rw [historyEq,positionEq]
            simp
          exact ⟨r,generation,pid,peer,recorded,native,pidEq,chosen,
            before.vacant.1,before.vacant.2,before.aligned,mem_pendingAt.mpr member⟩

/-- Security: every admitted ticket has exactly one native-backed pending
location or recorded terminal at an ordinary current accounting point. -/
theorem accounted_partition (before : CompleteCarrier.Accounted h ledger debts locals w)
    (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧ StatusEvidence h ledger locals w ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=before.entry.core.total_partition born
  exact ⟨status,member,accounted_status before member,unique⟩

/-- Security: while plaintext is held by staging, every admitted ticket has
one status on the same ledger; held tickets retain the actual take receipt
and the current vacant queue, including before any later Stop. -/
theorem selected_partition
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧ StatusEvidence h ledger locals w ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=before.core.total_partition born
  exact ⟨status,member,selected_status before member,unique⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
