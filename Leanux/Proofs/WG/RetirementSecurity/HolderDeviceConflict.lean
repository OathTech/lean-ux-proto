import Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
import Leanux.Proofs.WG.RetirementSecurity.HolderBulkRemoval

/-! Actual identity-conflict cleanup pays the lookup loan before detaching
its separate base peer reference. Exact key credit remains protected through
both payments and the real key-slot clearing/drain path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open StackOwnership DurableHolders

abbrev conflict (key : Key) : WG.M Unit :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key

theorem conflict_keys (key : Key) : Hoare (conflict key) (Entry temporary carriers loans)
    (fun _ w=>HolderAccount temporary w ∧ Allocated w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  change ((do
    let peer ← pubkeyLookup key
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer : WG.M Unit).run w).run a=.ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,lookup,tail⟩ := run
  have held := (hoare_iff_run_ambient _ _ _).mp (HolderConsume.pubkey key) w a peer u c before.1.1 lookup
  have allocation := Allocated.native (pubkeyLookupPrefix_erases key)
    (pubkeyLookupPrefix_preserves_ambient allocationAmbient key) before.1.2.1 a c lookup
  cases peer with
  | none=>
    change Except.ok (((),u),CounterWindow.record c .setDevOldPeer false)=.ok (((),v),b) at tail
    cases tail
    exact ⟨held.1,allocation⟩
  | some pid=>
    obtain ⟨holders,originalFunded,originalStable⟩ := before.2.1.1.1
    obtain ⟨o,slot,funded,stable,coherent,unique,selected⟩ := BaseLookupRemoval.lookup_selected
      key originalFunded originalStable before.2.1.1.2.1 before.2.1.1.2.2 a c lookup
    subst pid
    change ((peerPut (some o.slot) >>= fun _=>peerRemove (some o.slot)).run u).run
      (CounterWindow.record c .setDevOldPeer true)=.ok (((),v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,payment,removal⟩ := tail
    cases ignored
    have paidKeys := (hoare_iff_run_ambient _ _ _).mp (HolderConsume.payment o.slot)
      u _ () z d ⟨held.1,held.2 o.slot rfl⟩ payment
    have paidAllocation := Allocated.native (peerPutMixed_erases (some o.slot))
      (peerPutMixed_allocation (some o.slot)) allocation _ d payment
    obtain ⟨paidPeers,paidStable⟩ := DeviceBoundary.pay_funded o funded stable _ d payment
    have anchors : SlotPeerReferences holders loans w :=
      KeySlotLiveness.references before.2.2 originalFunded before.2.1.1.2.1 before.2.1.1.2.2
    have afterLookup := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.pubkey_lookup key)
      w a (some o.slot) u c anchors lookup
    have afterPayment := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.peer_put (some o.slot))
      u _ () z d afterLookup payment
    have keys := HolderRemoval.some_peer paidKeys paidPeers paidStable afterPayment o.slot unique selected d b removal
    exact ⟨keys.1.2.1,Allocated.native (PeerRemovalCall.erases (.remove (some o.slot)))
      (PeerRemovalCall.allocation (.remove (some o.slot))) paidAllocation d b removal⟩

theorem conflict_entry (key : Key) : Preserves (Entry temporary carriers loans) (conflict key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have keys := (hoare_iff_run_ambient _ _ _).mp (conflict_keys key) w a result v b before run
  have peer := (hoare_iff_run_ambient _ _ _).mp (DeviceBoundary.keyConflict_entry key)
    w a result v b before.2.1.1 run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.keyConflict_keeps) key)
    w a result v b before.1.2.2 run
  have physical := HolderStopPhysical.optional_cell before.2.1.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DevicePhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical.keyConflict_cell) key)
      w a result v b run)
  have live := (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.device_key_conflict key)
    w a result v b before.2.2 run
  exact ⟨⟨keys.1,keys.2,slots⟩,⟨peer,physical,slots⟩,live⟩

theorem remove_all : Preserves (Entry temporary carriers loans) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨holders,funded,stable⟩ := before.2.1.1.1
  have anchored := KeySlotLiveness.references before.2.2 funded before.2.1.1.2.1 before.2.1.1.2.2
  have keys := HolderRemoval.all_peers before.1.1 funded stable anchored a b run
  have allocation := Allocated.native (PeerRemovalCall.erases .removeAll)
    (PeerRemovalCall.allocation .removeAll) before.1.2.1 a b run
  have peer := (hoare_iff_run_ambient _ _ _).mp DeviceBoundary.removeAll_entry w a () v b before.2.1.1 run
  have slots := (hoare_iff_run_ambient _ _ _).mp CurrentSlots.Removal.removeAll w a () v b before.1.2.2 run
  have physical := HolderStopPhysical.optional_cell before.2.1.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp ConfigurationPhysical.removeAll_cell w a () v b run)
  have live := (hoare_iff_run_ambient _ _ _).mp KeySlotLiveness.all_peers w a () v b before.2.2 run
  exact ⟨⟨keys.2.1,allocation,slots⟩,⟨peer,physical,slots⟩,live⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
