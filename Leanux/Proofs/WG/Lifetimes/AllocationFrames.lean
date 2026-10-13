import Leanux.Proofs.WG.Lifetimes.KeypairAllocation
import Leanux.Proofs.WG.Lifetimes.PacketAllocation

/-! The metadata omitted by identityView. Together these projections support
frames without requiring all Device contents to be unchanged. History transport
is separate: access-only suffixes retain the released-identity sets. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

@[ext] structure DeviceAllocationMetadata where
  epoch : Nat
  nextPeer : Nat
  nextKeypair : Nat
  nextPacket : Nat

def deviceAllocationMetadata (d : Device) : DeviceAllocationMetadata :=
  ⟨d.ifindex, d.nextPeer, d.nextKeypairId, d.nextSkb⟩

@[ext] structure AllocationMetadata where
  keyCounter : Nat
  nextEpoch : Nat
  device : Option DeviceAllocationMetadata

def allocationMetadata (w : World) : AllocationMetadata :=
  ⟨w.k.keypairCounter, w.k.netIfindexNext, w.k.wg.map deviceAllocationMetadata⟩

theorem allocationMetadata_device {w v : World} (hm : allocationMetadata v = allocationMetadata w)
    (hv : v.k.wg = some e) :
    ∃ d, w.k.wg = some d ∧ deviceAllocationMetadata e = deviceAllocationMetadata d := by
  have he := congrArg AllocationMetadata.device hm
  cases hd : w.k.wg with
  | none => simp [allocationMetadata, hd, hv] at he
  | some d => exact ⟨d, rfl, by simpa [allocationMetadata, hd, hv] using he⟩

theorem AllocationInv.congr (hi : AllocationInv h w)
    (he : identityView v = identityView w) (hm : allocationMetadata v = allocationMetadata w) :
    AllocationInv h v := by
  have hp : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst he
  have hk : keypairResidents v = keypairResidents w := congrArg (fun s : IdentityView => s.2.1) he
  have ht : packetResidents v = packetResidents w := congrArg (fun s : IdentityView => s.2.2) he
  have hkc : v.k.keypairCounter = w.k.keypairCounter := congrArg AllocationMetadata.keyCounter hm
  have hne : v.k.netIfindexNext = w.k.netIfindexNext := congrArg AllocationMetadata.nextEpoch hm
  refine ⟨⟨hi.release.1.congr he, he ▸ hi.release.2⟩, hi.peer.congr hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e hv i p hvp
    obtain ⟨d, hd, hmeta⟩ := allocationMetadata_device hm hv
    have hn : e.nextPeer = d.nextPeer := congrArg DeviceAllocationMetadata.nextPeer hmeta
    have hl : (Peers.snapshot w).slots i = some p.internalId := by
      rw [← hp]; simp [Peers.snapshot, hv, hvp]
    simp only [Peers.snapshot, hd, Option.bind_some] at hl
    cases hx : d.peers[i]? with
    | none => simp [hx] at hl
    | some old => rw [hn]; exact hi.peerSlots d hd i old hx
  · intro i stamp hl
    change keypairResidents v i = some stamp at hl
    change stamp ≤ v.k.keypairCounter
    rw [hkc]
    exact hi.keyBounded i stamp (by simpa only [keyStore, hk] using hl)
  · intro stamp hs
    rw [hkc]; exact hi.keyPast stamp hs
  · intro e hv i k hvk
    obtain ⟨d, hd, hmeta⟩ := allocationMetadata_device hm hv
    have hn : e.nextKeypairId = d.nextKeypairId := congrArg DeviceAllocationMetadata.nextKeypair hmeta
    have hl : keypairResidents w i = some k.internalId := by
      rw [← hk]; simp [keypairResidents, hv, hvk]
    simp only [keypairResidents, hd, Option.bind_some] at hl
    cases hx : d.keypairs[i]? with
    | none => simp [hx] at hl
    | some old => rw [hn]; exact hi.keySlots d hd i old hx
  · intro e hv s stamp hs
    obtain ⟨d, hd, hmeta⟩ := allocationMetadata_device hm hv
    have hn : e.nextSkb = d.nextSkb := congrArg DeviceAllocationMetadata.nextPacket hmeta
    have hl : packetResidents w s = some (e.ifindex, stamp) := by
      rw [← ht, packetResidents_device hv, hs]; rfl
    rw [packetResidents_device hd] at hl
    cases hx : (Packets.deviceStore d).slots s with
    | none => simp [hx] at hl
    | some old =>
      simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      change stamp ≤ e.nextSkb
      rw [hn, ← hl.2]
      exact hi.packetBounded d hd s old hx
  · intro e hv
    obtain ⟨d, hd, hmeta⟩ := allocationMetadata_device hm hv
    have hn : e.ifindex = d.ifindex := congrArg DeviceAllocationMetadata.epoch hmeta
    rw [hn, hne]; exact hi.epochBounded d hd
  · intro stamp hs
    rw [hne]; exact hi.packetPastEpoch stamp hs
  · intro e hv stamp hs
    obtain ⟨d, hd, hmeta⟩ := allocationMetadata_device hm hv
    have hn : e.nextSkb = d.nextSkb := congrArg DeviceAllocationMetadata.nextPacket hmeta
    have hep : e.ifindex = d.ifindex := congrArg DeviceAllocationMetadata.epoch hmeta
    rw [hn]
    exact hi.packetPast d hd stamp (hep ▸ hs)

/-- Reuse an existing safety proof when the observed suffix contains no new
releases. This is not applicable to release helpers without additional bounds. -/
theorem AllocationInv.history (hi : AllocationInv h w) (hr : ReleaseInv g w)
    (hp : ∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.peer?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.peer?) s)
    (hk : ∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.keypair?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) s)
    (ht : ∀ s, AccessEvent.Released (g.filterMap LifetimeEvent.packet?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.packet?) s) : AllocationInv g w :=
  ⟨hr, ⟨hr.1.peer, hi.peer.bounded, fun s hs => hi.peer.pastBounded s ((hp s).mp hs)⟩,
    hi.peerSlots, hi.keyBounded, fun s hs => hi.keyPast s ((hk s).mp hs), hi.keySlots,
    hi.packetBounded, hi.epochBounded, fun s hs => hi.packetPastEpoch s ((ht s).mp hs),
    fun d hd s hs => hi.packetPast d hd s ((ht _).mp hs)⟩

/-- An observed access-only action can reuse its release-safe contract. The
original action frames both identities and metadata, and the observer itself
must establish that no new release entered any family history. -/
theorem allocation_access (hg : AmbientSpec ReleaseInv P g Q) (he : ErasesPrefix g a)
    (hv : ∀ w x v, P (identityView w) → a.run w = .ok (x, v) →
      (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w))
    (hp : ∀ w h s, AccessEvent.Released ((runPrefix g w h).2.filterMap LifetimeEvent.peer?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.peer?) s)
    (hk : ∀ w h s, AccessEvent.Released ((runPrefix g w h).2.filterMap LifetimeEvent.keypair?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) s)
    (ht : ∀ w h s, AccessEvent.Released ((runPrefix g w h).2.filterMap LifetimeEvent.packet?) s ↔
      AccessEvent.Released (h.filterMap LifetimeEvent.packet?) s) : AmbientSpec AllocationInv P g Q := by
  intro w h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := hg w h ⟨hi.1.release, hi.2⟩
  refine ⟨suffix, hsuf, hsafe, ?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    have ho : a.run w = .ok out := (he w h).symm.trans hr
    have hf := hv w out.1 out.2 hi.2 ho
    have hi' := hi.1.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)
    have hq : ReleaseInv (runPrefix g w h).2 out.2 ∧ Q out.1 (identityView out.2) := by
      simpa only [hr] using hout
    exact ⟨hi'.history hq.1 (hp w h) (hk w h) (ht w h), hq.2⟩

end Leanux.Proofs.WG.Lifetimes
