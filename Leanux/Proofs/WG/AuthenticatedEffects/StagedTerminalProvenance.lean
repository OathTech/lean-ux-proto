import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveAssignment
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalReceipts

/-! Terminal labels are meaningful only when bound to their actual source
receipt and ticket. This relation is separate from Core and Step, which by
themselves allow arbitrary terminal constructors. Initialized transport and
the source of each receipt remain obligations of the enclosing driver. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal HandshakeSecurity.StagedConservation

def Lineage (history : List Event) (ticket : Ticket) (batch ordinal generation skb : Nat)
    (material : DataPacket) : Prop :=
  Origin history batch ordinal generation skb material ∧
    ∃ pid stamp, Born history generation pid stamp ticket material.plaintext ∧ material.peer = pid

def AllocatedBorn (history : List Event) (ticket : Ticket) (batch ordinal : Nat) : Prop :=
  ∃ generation skb material, Lineage history ticket batch ordinal generation skb material

def AllocationLinks (history : List Event) (ledger : Ledger) : Prop :=
  ∀ ticket batch ordinal, (ticket,Status.pending (.allocated batch ordinal)) ∈ ledger →
    AllocatedBorn history ticket batch ordinal

/-- Evidence is checked at the terminal event's strict prefix. Native queue
alignment and allocated backing use that receipt's own entry state. -/
inductive At (history : List Event) : Event → Ticket → Staged.Obligations.Terminal → Prop where
  | overflow (pid : PeerId) (r : WGRunWitness Unit)
      (native : r.Valid (xmitTrim pid))
      (part : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after)
      (generation : Nat) (epoch : Packets.epoch r.before = some generation)
      (tickets : List Ticket) (aligned : Aligned (Born history generation pid part.stamp) tickets part.packets)
      (member : ticket ∈ tickets.take part.removed) :
      At history (.stagedDisposal (.overflow pid r)) ticket (.counted history.length .overflow)
  | purge (pid : PeerId) (r : WGRunWitness Unit)
      (native : r.Valid (purgeStagedPackets pid))
      (part : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after)
      (whole : part.removed = part.packets.length)
      (generation : Nat) (epoch : Packets.epoch r.before = some generation)
      (tickets : List Ticket) (aligned : Aligned (Born history generation pid part.stamp) tickets part.packets)
      (member : ticket ∈ tickets) :
      At history (.stagedDisposal (.purge pid r)) ticket (.counted history.length .purge)
  | released (peer : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
      (native : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
      (pid : PeerId) (p : Peer) (result : r.value = some (pid,p))
      (generation : Nat) (epoch : Packets.epoch r.before = some generation)
      (tickets : List Ticket) (aligned : Aligned (Born history generation pid p.internalId) tickets p.staged)
      (member : ticket ∈ tickets) :
      At history (.stagedDisposal (.release peer r)) ticket (.counted history.length .finalRelease)
  | socket (r : Completion.SocketReceipt) (native : r.Valid)
      (batch ordinal generation : Nat) (material : DataPacket)
      (lineage : Lineage history ticket batch ordinal generation r.id material)
      (backed : Backed history batch ordinal r.packet.before.wg) :
      At history (.old (.socket r)) ticket (.socket history.length (r.socket.value == 0))
  | refused (r : SendResult.Receipt) (native : r.Valid) (failed : r.run.value = false)
      (peer : RunWitness Peer) (read : peer.Valid (liftWG (getPeer r.pid)))
      (entry : peer.before = r.run.before)
      (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
      (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6)
      (batch ordinal generation : Nat) (material : DataPacket)
      (lineage : Lineage history ticket batch ordinal generation r.skb material)
      (backed : Backed history batch ordinal r.packet.before.wg) :
      At history (.sendResult r) ticket (.sendRefused history.length)
  | disposed (r : Terminal.Receipt) (native : r.Valid)
      (batch ordinal generation : Nat) (material : DataPacket)
      (lineage : Lineage history ticket batch ordinal generation r.skb material)
      (backed : Backed history batch ordinal r.run.before.wg) :
      At history (.terminalDrop r) ticket (.disposed history.length r.reason)

def Evidence (history : List Event) (ticket : Ticket) (outcome : Staged.Obligations.Terminal) : Prop :=
  ∃ before event after, history = before ++ event :: after ∧ At before event ticket outcome

def Justified (history : List Event) (ledger : Ledger) : Prop :=
  ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger → Evidence history ticket outcome

theorem Evidence.here (atCut : At history event ticket outcome) :
    Evidence (history ++ [event]) ticket outcome := ⟨history,event,[],rfl,atCut⟩

theorem Evidence.append (before : Evidence history ticket outcome) (suffix : List Event) :
    Evidence (history ++ suffix) ticket outcome := by
  obtain ⟨prior,event,after,rfl,evidence⟩ := before
  exact ⟨prior,event,after ++ suffix,by simp only [List.append_assoc,List.cons_append],evidence⟩

theorem Justified.append (before : Justified history ledger) (suffix : List Event) :
    Justified (history ++ suffix) ledger := fun _ _ member => (before _ _ member).append suffix

theorem Lineage.append (before : Lineage history ticket batch ordinal generation skb material)
    (suffix : List Event) : Lineage (history ++ suffix) ticket batch ordinal generation skb material := by
  obtain ⟨origin,pid,stamp,born,peer⟩ := before
  exact ⟨origin.append suffix,pid,stamp,born.append suffix,peer⟩

theorem AllocatedBorn.append (before : AllocatedBorn history ticket batch ordinal) (suffix : List Event) :
    AllocatedBorn (history ++ suffix) ticket batch ordinal := by
  obtain ⟨generation,skb,material,lineage⟩ := before
  exact ⟨generation,skb,material,lineage.append suffix⟩

theorem AllocationLinks.append (before : AllocationLinks history ledger) (suffix : List Event) :
    AllocationLinks (history ++ suffix) ledger := fun _ _ _ member => (before _ _ _ member).append suffix

/-- Backing at the actual cut must identify the same allocation ordinal as
the ticket's birth link; an equal payload at another ordinal is insufficient. -/
theorem AllocatedBorn.at_origin (before : AllocatedBorn history ticket batch ordinal)
    (origin : Origin history batch ordinal generation skb material) :
    Lineage history ticket batch ordinal generation skb material := by
  obtain ⟨otherGeneration,otherId,otherMaterial,other,born⟩ := before
  obtain ⟨rfl,rfl,rfl⟩ := other.unique origin
  exact ⟨other,born⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
