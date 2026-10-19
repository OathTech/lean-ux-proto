import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationBacking

/-! Native map erasure is separate from terminal classification. A physical
free cannot preserve allocated backing unless every still-pending obligation
is proved to refer to another cell of the current device epoch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

/-- The exact native free preserves the epoch, erases its own cell and leaves
every other packet's immutable material unchanged. -/
theorem free_views (receipt : Terminal.Receipt) (valid : receipt.Valid) :
    Packets.epoch receipt.run.after.wg = Packets.epoch receipt.run.before.wg ∧
    PacketMaterial.view receipt.run.after.wg receipt.skb = none ∧
    ∀ id, id ≠ receipt.skb →
      PacketMaterial.view receipt.run.after.wg id = PacketMaterial.view receipt.run.before.wg id := by
  obtain ⟨device,packet,atDevice,_,after⟩ := valid.effects
  rw [after]
  refine ⟨?_,?_,?_⟩
  · simp [Packets.epoch,Packets.update,atDevice]
  · simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice]
  · intro id different
    simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice,
      Std.TreeMap.getElem?_erase,Ne.symm different]

/-- The location to be freed has no pending obligation in this device epoch.
Historical allocations from another epoch do not obstruct current cleanup. -/
def Unused (history : List CausalJournal.Event) (ledger : Ledger) (w : WGWorld)
    (skb : SkbId) : Prop :=
  ∀ ticket position ordinal, (ticket,Status.pending (.allocated position ordinal)) ∈ ledger →
    ∀ generation value, Origin history position ordinal generation skb value →
      Packets.epoch w ≠ some generation

/-- A source-proved nonalias condition is essential: physical deletion alone
does not justify forgetting a pending ticket. -/
theorem Resident.free (before : Resident history ledger receipt.run.before.wg)
    (valid : (receipt : Terminal.Receipt).Valid)
    (unused : Unused history ledger receipt.run.before.wg receipt.skb) :
    Resident history ledger receipt.run.after.wg := by
  obtain ⟨epoch,_,other⟩ := free_views receipt valid
  intro ticket position ordinal member
  obtain ⟨generation,id,value,origin,time,cell⟩ := before ticket position ordinal member
  have different : id ≠ receipt.skb := by
    intro same
    subst id
    exact unused ticket position ordinal member generation value origin time
  exact ⟨generation,id,value,origin,epoch.trans time,(other id different).trans cell⟩

/-- Any chosen native terminal receipt identifies its input allocation stamp;
the epoch is taken at the free itself, not from a later resident lookup. -/
theorem receipt_stamp (receipt : Terminal.Receipt)
    (epoch : Packets.epoch receipt.run.before.wg = some generation) :
    receipt.stamp = (generation,receipt.skb + 1) := by
  simp only [Terminal.Receipt.stamp,packetStamp]
  change ((Packets.epoch receipt.run.before.wg).getD 0,receipt.skb + 1) = _
  rw [epoch]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
