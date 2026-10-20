import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeTrimFrames

/-! The exact removed prefix stays in the fixed ledger until its original
overflow receipt; retained and removed positions keep their birth evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal
open Transmit.Front.Residual

def TrimStatusEvidence (h : History) (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (removed : Nat) (original current : WGWorld) (ticket : Ticket) : Status → Prop
  | .pending (.staged generation owner stamp)=>
      Aligned (Born h generation owner stamp) (pendingAt (.staged generation owner stamp) ledger)
        (stagedPackets generation owner stamp original) ∧
      stagedPackets generation owner stamp current=
        (stagedPackets generation owner stamp original).drop (if owner=pid then removed else 0) ∧
      ticket∈pendingAt (.staged generation owner stamp) ledger
  | status=>StatusEvidence h ledger locals current ticket status

theorem trim_status (before : CompleteCarrier.Accounted h ledger debts locals original)
    (physical : Staged.Obligations.Physical h ledger debts current) (native : NativeReady.Inv locals current)
    (queues : ∀generation owner stamp,stagedPackets generation owner stamp current=
      (stagedPackets generation owner stamp original).drop (if owner=pid then removed else 0))
    (member : (ticket,status)∈ledger) :
    TrimStatusEvidence h ledger locals pid removed original current ticket status := by
  cases status with
  | terminal outcome=>exact before.entry.justified ticket outcome member
  | pending location=>
      cases location with
      | staged generation owner stamp=>exact ⟨before.entry.core.queues generation owner stamp,
          queues generation owner stamp,mem_pendingAt.mpr member⟩
      | selected position=>
          have impossible:=mem_pendingAt.mpr member
          rw [before.entry.noSelected position] at impossible
          cases impossible
      | allocated batch ordinal=>
          obtain ⟨epoch,id,material,origin,time,cell⟩:=physical.resident ticket batch ordinal member
          obtain ⟨packet,resident,_⟩:=Option.map_eq_some_iff.mp cell
          exact ⟨epoch,id,material,(before.entry.allocationLinks ticket batch ordinal member).at_origin origin,
            time,cell,native.2.1 id packet resident⟩

/-- Security: completed native trim iterations retain the unique original
ticket for each admission. The exact removed prefix remains pending on that
ledger until its overflow receipt; allocated cells and terminal evidence keep
their current native and historical backing. -/
theorem trim_partition (cut : TrimCut h ledger debts locals pid w a n v b)
    (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧ TrimStatusEvidence h ledger locals pid n w v ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=cut.entry.entry.core.total_partition born
  obtain ⟨d,p,device,resident⟩:=cut.read
  exact ⟨status,member,trim_status cut.entry cut.packet_account.2 cut.packet_account.1
    (cut.path.staged_packets device resident) member,unique⟩

/-- Security: after a queue removal and before its counter charge, the
removed prefix has n+1 positions and still has its unique pending tickets.
No receipt or terminal outcome is invented for this silent native write. -/
theorem trim_drop_partition (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (excess : p.staged.length>MAX_STAGED_PACKETS) (born : ticket∈births h) :
    ∃status,(ticket,status)∈ledger ∧
      TrimStatusEvidence h ledger locals pid (n+1) w (droppedWorld pid p d v) ticket status ∧
      ∀other,(ticket,other)∈ledger→other=status := by
  obtain ⟨status,member,unique⟩:=cut.entry.entry.core.total_partition born
  have account:=cut.dropped_packet_account device resident
  exact ⟨status,member,trim_status cut.entry account.2 account.1
    (cut.dropped_staged_packets device resident excess) member,unique⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
