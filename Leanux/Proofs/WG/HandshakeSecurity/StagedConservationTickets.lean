import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedTicketIdentity

/-! Fixed-ticket splitting at native counted disposal. Both sides use the
same incoming ordered ticket list. These local facts supply the forward ledger
transition; they do not infer completeness from remaining queue membership. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity.Staged TransmitSecurity.Staged.Origins

variable {R : Ticket → Packet → Prop} {tickets : List Ticket} {packets : List Packet}

theorem aligned_length (aligned : Aligned R tickets packets) : tickets.length = packets.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons,ih]

theorem aligned_take (aligned : Aligned R tickets packets) (n : Nat) :
    Aligned R (tickets.take n) (packets.take n) := by
  induction n generalizing tickets packets with
  | zero => exact .nil
  | succ n ih =>
    cases aligned with
    | nil => exact .nil
    | cons head tail => exact .cons head (ih tail)

theorem aligned_drop (aligned : Aligned R tickets packets) (n : Nat) :
    Aligned R (tickets.drop n) (packets.drop n) := by
  induction n generalizing tickets packets with
  | zero => exact aligned
  | succ n ih =>
    cases aligned with
    | nil => exact .nil
    | cons _ tail => exact ih tail

/-- Every input ticket is in exactly one side of the actual source partition.
In particular, equal packet values cannot merge or relabel their obligations. -/
theorem tickets_partition (unique : tickets.Nodup) (n : Nat) :
    tickets.take n ++ tickets.drop n = tickets ∧
    (tickets.take n).Nodup ∧ (tickets.drop n).Nodup ∧
    (∀ ticket ∈ tickets.take n, ticket ∉ tickets.drop n) ∧
    (∀ ticket, ticket ∈ tickets ↔ ticket ∈ tickets.take n ∨ ticket ∈ tickets.drop n) := by
  have split := List.take_append_drop n tickets
  have nodup : (tickets.take n ++ tickets.drop n).Nodup := split.symm ▸ unique
  obtain ⟨left,right,disjoint⟩ := List.nodup_append.mp nodup
  refine ⟨split,left,right,?_,?_⟩
  · intro ticket first second
    exact disjoint ticket first ticket second rfl
  · intro ticket
    simpa only [split] using
      (List.mem_append : ticket ∈ tickets.take n ++ tickets.drop n ↔
        ticket ∈ tickets.take n ∨ ticket ∈ tickets.drop n)

/-- The native counted partition transfers its exact discarded prefix to the
terminal side and retains the exact suffix under the same peer allocation. -/
theorem native_partition (p : StagedDisposal.Partition pid w v)
    (unique : tickets.Nodup) (aligned : Aligned R tickets p.packets) :
    Aligned R (tickets.take p.removed) (p.packets.take p.removed) ∧
    Aligned R (tickets.drop p.removed) (p.packets.drop p.removed) ∧
    (tickets.take p.removed).length = p.removed ∧
    tickets.take p.removed ++ tickets.drop p.removed = tickets ∧
    (∀ ticket ∈ tickets.take p.removed, ticket ∉ tickets.drop p.removed) ∧
    stagedAt v pid = some (p.stamp,p.packets.drop p.removed) ∧
    (∃ count, dropped w = some count ∧ dropped v = some (count+(tickets.take p.removed).length)) := by
  have length := aligned_length aligned
  have bound : p.removed ≤ tickets.length := by rw [length]; exact p.bounded
  have count : (tickets.take p.removed).length = p.removed := by simp only [List.length_take,Nat.min_eq_left bound]
  obtain ⟨split,_,_,disjoint,_⟩ := tickets_partition unique p.removed
  exact ⟨aligned_take aligned _,aligned_drop aligned _,count,split,disjoint,p.after,by simpa only [count] using p.charged⟩

/-- Successful full purge consumes every incoming ticket once; it is not a
frame which merely drops all queue obligations. The actual counter is exposed. -/
theorem native_purge (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (purgeStagedPackets pid)) :
    ∃ p : StagedDisposal.Partition pid r.before r.after,
      p.removed = p.packets.length ∧ ∀ (tickets : List Ticket), tickets.Nodup →
      Aligned R tickets p.packets → tickets.take p.removed = tickets ∧
        tickets.drop p.removed = [] ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+tickets.length)) := by
  obtain ⟨p,whole⟩ := StagedDisposal.purge_exact pid r valid
  refine ⟨p,whole,?_⟩
  intro tickets _ aligned
  have count : p.removed = tickets.length := whole.trans (aligned_length aligned).symm
  refine ⟨by simp [count],by simp [count],?_⟩
  simpa only [count] using p.charged

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation
