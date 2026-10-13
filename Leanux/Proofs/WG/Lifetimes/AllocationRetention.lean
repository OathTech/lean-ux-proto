import Leanux.Proofs.WG.Lifetimes.AllocationFrames
import Leanux.Proofs.WG.Lifetimes.ReleaseCalls

/-! Fixed-metadata transport for access and release calls. Safety of failed
prefixes is reused from ReleaseInv; successful executions additionally retain
resident identities and account for every newly released identity at entry. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def ResidentsRetained (before after : ι → Option κ) : Prop :=
  ∀ i stamp, after i = some stamp → before i = some stamp

structure AllocationRetention (w v : World) : Prop where
  metadata : allocationMetadata v = allocationMetadata w
  peer : Retained (Peers.snapshot w) (Peers.snapshot v)
  key : ResidentsRetained (keypairResidents w) (keypairResidents v)
  packet : ResidentsRetained (packetResidents w) (packetResidents v)

def ReleasedFrom (before after : List (AccessEvent ι κ)) (resident : ι → Option κ) : Prop :=
  ∀ stamp, AccessEvent.Released after stamp →
    AccessEvent.Released before stamp ∨ ∃ i, resident i = some stamp

structure ReleaseOrigin (h g : List LifetimeEvent) (w : World) : Prop where
  peer : ReleasedFrom (h.filterMap LifetimeEvent.peer?) (g.filterMap LifetimeEvent.peer?) (Peers.snapshot w).slots
  key : ReleasedFrom (h.filterMap LifetimeEvent.keypair?) (g.filterMap LifetimeEvent.keypair?) (keypairResidents w)
  packet : ReleasedFrom (h.filterMap LifetimeEvent.packet?) (g.filterMap LifetimeEvent.packet?) (packetResidents w)

theorem packet_resident_store {w : World} {slot : Packets.Slot} {stamp : PacketStamp}
    (hs : packetResidents w slot = some stamp) :
    ∃ d n, w.k.wg = some d ∧ stamp = (d.ifindex, n) ∧ (Packets.deviceStore d).slots slot = some n := by
  cases hd : w.k.wg with
  | none => simp [packetResidents, hd] at hs
  | some d =>
    rw [packetResidents_device hd] at hs
    cases hn : (Packets.deviceStore d).slots slot with
    | none => simp [hn] at hs
    | some n =>
      simp only [hn, Option.map_some, Option.some.injEq] at hs
      exact ⟨d, n, rfl, hs.symm, hn⟩

theorem AllocationInv.retained (hi : AllocationInv h w) (hr : ReleaseInv g v)
    (hs : AllocationRetention w v) (ho : ReleaseOrigin h g w) : AllocationInv g v := by
  have hkc : v.k.keypairCounter = w.k.keypairCounter := congrArg AllocationMetadata.keyCounter hs.metadata
  have hne : v.k.netIfindexNext = w.k.netIfindexNext := congrArg AllocationMetadata.nextEpoch hs.metadata
  refine ⟨hr, ⟨hr.1.peer, hs.peer.bounded hi.peer.bounded, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro stamp released
    rw [hs.peer.1]
    rcases ho.peer stamp released with old | ⟨i, live⟩
    · exact hi.peer.pastBounded stamp old
    · exact hi.peer.bounded i stamp live
  · intro e hv i p hl
    obtain ⟨d, hd, hm⟩ := allocationMetadata_device hs.metadata hv
    have hn : e.nextPeer = d.nextPeer := congrArg DeviceAllocationMetadata.nextPeer hm
    have old := hs.peer.2 i p.internalId (by simp [Peers.snapshot, hv, hl])
    simp only [Peers.snapshot, hd, Option.bind_some] at old
    cases hx : d.peers[i]? with
    | none => simp [hx] at old
    | some p => rw [hn]; exact hi.peerSlots d hd i p hx
  · intro i stamp hl
    change stamp ≤ v.k.keypairCounter
    rw [hkc]
    exact hi.keyBounded i stamp (hs.key i stamp hl)
  · intro stamp released
    rw [hkc]
    rcases ho.key stamp released with old | ⟨i, live⟩
    · exact hi.keyPast stamp old
    · exact hi.keyBounded i stamp live
  · intro e hv i k hl
    obtain ⟨d, hd, hm⟩ := allocationMetadata_device hs.metadata hv
    have hn : e.nextKeypairId = d.nextKeypairId := congrArg DeviceAllocationMetadata.nextKeypair hm
    have old := hs.key i k.internalId (by simp [keypairResidents, hv, hl])
    simp only [keypairResidents, hd, Option.bind_some] at old
    cases hx : d.keypairs[i]? with
    | none => simp [hx] at old
    | some k => rw [hn]; exact hi.keySlots d hd i k hx
  · intro e hv i stamp hl
    obtain ⟨d, hd, hm⟩ := allocationMetadata_device hs.metadata hv
    have hn : e.nextSkb = d.nextSkb := congrArg DeviceAllocationMetadata.nextPacket hm
    have old := hs.packet i (e.ifindex, stamp) (by rw [packetResidents_device hv, hl]; rfl)
    rw [packetResidents_device hd] at old
    cases hx : (Packets.deviceStore d).slots i with
    | none => simp [hx] at old
    | some n =>
      simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at old
      change stamp ≤ e.nextSkb
      rw [hn, ← old.2]
      exact hi.packetBounded d hd i n hx
  · intro e hv
    obtain ⟨d, hd, hm⟩ := allocationMetadata_device hs.metadata hv
    have hn : e.ifindex = d.ifindex := congrArg DeviceAllocationMetadata.epoch hm
    rw [hn, hne]; exact hi.epochBounded d hd
  · intro stamp released
    rw [hne]
    rcases ho.packet stamp released with old | ⟨i, live⟩
    · exact hi.packetPastEpoch stamp old
    · obtain ⟨d, n, hd, rfl, _⟩ := packet_resident_store live
      exact hi.epochBounded d hd
  · intro e hv stamp released
    obtain ⟨d, hd, hm⟩ := allocationMetadata_device hs.metadata hv
    have hep : e.ifindex = d.ifindex := congrArg DeviceAllocationMetadata.epoch hm
    have hn : e.nextSkb = d.nextSkb := congrArg DeviceAllocationMetadata.nextPacket hm
    rw [hn]
    rcases ho.packet (e.ifindex, stamp) released with old | ⟨i, live⟩
    · exact hi.packetPast d hd stamp (hep ▸ old)
    · rw [packetResidents_device hd] at live
      cases hx : (Packets.deviceStore d).slots i with
      | none => simp [hx] at live
      | some n =>
        simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at live
        rw [← live.2]; exact hi.packetBounded d hd i n hx

theorem allocation_retained (hg : PrefixPreserves ReleaseInv LifetimeEvent.Safe g)
    (he : ErasesPrefix g a)
    (hs : ∀ w x v, a.run w = .ok (x, v) → AllocationRetention w v)
    (ho : ∀ w h, ReleaseOrigin h (runPrefix g w h).2 w) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe g := by
  intro w h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := hg w h hi.release
  refine ⟨suffix, hsuf, hsafe, ?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    exact hi.retained (by simpa only [hr] using hout)
      (hs w out.1 out.2 ((he w h).symm.trans hr)) (ho w h)

end Leanux.Proofs.WG.Lifetimes
