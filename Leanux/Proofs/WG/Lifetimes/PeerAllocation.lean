import Leanux.Proofs.WG.Lifetimes.PeerAllocationFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The existing whole peer-creation observer, focused into the mixed history.
Its failed-prefix proof is reused intact; only successful state transport is
new. Allocation bounds do not assert scalar-reference ownership or lifecycle
closure. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def PeerSlotsBounded (w : World) : Prop :=
  ∀ d, w.k.wg = some d → ∀ i p, d.peers[i]? = some p → i < d.nextPeer

theorem PeerCreationGeometry.counters (hg : PeerCreationGeometry w result v) :
    v.k.keypairCounter = w.k.keypairCounter ∧ v.k.netIfindexNext = w.k.netIfindexNext := by
  have hk := congrArg AllocationMetadata.keyCounter hg.2.1
  have hn := congrArg AllocationMetadata.nextEpoch hg.2.1
  cases result <;> exact ⟨hk, hn⟩

theorem PeerCreationGeometry.device (hg : PeerCreationGeometry w result v)
    (hv : v.k.wg = some e) :
    ∃ d, w.k.wg = some d ∧ e.ifindex = d.ifindex ∧
      e.nextKeypairId = d.nextKeypairId ∧ e.nextSkb = d.nextSkb ∧
      e.nextPeer = (match result with | .error _ => d.nextPeer | .ok pid => pid + 1) := by
  have hm := congrArg AllocationMetadata.device hg.2.1
  cases hd : w.k.wg with
  | none => cases result <;> simp [allocationMetadata, peerCreateMetadata, hd, hv] at hm
  | some d =>
    refine ⟨d, rfl, ?_⟩
    cases result <;>
      simp only [allocationMetadata, peerCreateMetadata, hd, hv, Option.map_some,
        Option.some.injEq] at hm
    all_goals exact ⟨congrArg DeviceAllocationMetadata.epoch hm,
      congrArg DeviceAllocationMetadata.nextKeypair hm,
      congrArg DeviceAllocationMetadata.nextPacket hm,
      congrArg DeviceAllocationMetadata.nextPeer hm⟩

theorem peerCreate_peerSlots (key : Key) (psk : Option Key) (w v : World)
    (result : Except Int PeerId) (hb : PeerSlotsBounded w)
    (hr : (peerCreate key psk).run w = .ok (result, v)) : PeerSlotsBounded v := by
  have hg := peerCreate_geometry key psk w v result hr
  have hp := Peers.peerCreate_exact key psk w v result hr
  intro e hv i p hl
  obtain ⟨d, hd, _, _, _, hn⟩ := hg.device hv
  have live : (Peers.snapshot v).slots i = some p.internalId := by simp [Peers.snapshot, hv, hl]
  cases result with
  | error err =>
    rw [hp] at live
    simp only [Peers.snapshot, hd, Option.bind_some] at live
    cases hx : d.peers[i]? with
    | none => simp [hx] at live
    | some old => rw [hn]; exact hb d hd i old hx
  | ok pid =>
    have hpid : d.nextPeer = pid := by simpa only [hd, Option.map_some, Option.some.injEq] using hg.2.2
    rw [hn]
    by_cases he : i = pid
    · subst i; exact Nat.lt_succ_self _
    · rw [hp] at live
      simp only [Store.allocate, if_neg he, Peers.snapshot, hd, Option.bind_some] at live
      cases hx : d.peers[i]? with
      | none => simp [hx] at live
      | some old =>
        have bound := hb d hd i old hx
        simp only at hn ⊢
        exact Nat.lt_trans (hpid ▸ bound) (Nat.lt_succ_self _)

/-- Replace only the peer component using its existing history-sensitive
contract. Other family histories and their resident identities are framed;
the original creation geometry supplies their unchanged bounds. -/
theorem AllocationInv.peerTransport (hi : AllocationInv h w)
    (hg : PeerCreationGeometry w result v)
    (hp : Peers.CreationInv (g.filterMap LifetimeEvent.peer?) v)
    (hb : PeerSlotsBounded v)
    (hkey : g.filterMap LifetimeEvent.keypair? = h.filterMap LifetimeEvent.keypair?)
    (hpacket : g.filterMap LifetimeEvent.packet? = h.filterMap LifetimeEvent.packet?) :
    AllocationInv g v := by
  have hk : keypairResidents v = keypairResidents w := congrArg Prod.fst hg.1
  have ht : packetResidents v = packetResidents w := congrArg Prod.snd hg.1
  obtain ⟨hkc, hne⟩ := hg.counters
  refine ⟨⟨⟨hp.access, ?_, ?_⟩, ?_⟩, hp, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hkey, hk] using hi.release.1.keypair
  · simpa only [hpacket, ht] using hi.release.1.packet
  · exact ⟨by simpa only [identityView, hk] using hi.release.2.1,
      by simpa only [identityView, ht] using hi.release.2.2⟩
  · intro i stamp hl
    change stamp ≤ v.k.keypairCounter
    rw [hkc]
    exact hi.keyBounded i stamp (by simpa only [keyStore, hk] using hl)
  · intro stamp hs
    rw [hkc]
    exact hi.keyPast stamp (hkey ▸ hs)
  · intro e hv i k hl
    obtain ⟨d, hd, _, hn, _, _⟩ := hg.device hv
    have old : keypairResidents w i = some k.internalId := by
      rw [← hk]; simp [keypairResidents, hv, hl]
    simp only [keypairResidents, hd, Option.bind_some] at old
    cases hx : d.keypairs[i]? with
    | none => simp [hx] at old
    | some k => rw [hn]; exact hi.keySlots d hd i k hx
  · intro e hv i stamp hl
    obtain ⟨d, hd, _, _, hn, _⟩ := hg.device hv
    have old : packetResidents w i = some (e.ifindex, stamp) := by
      rw [← ht, packetResidents_device hv, hl]; rfl
    rw [packetResidents_device hd] at old
    cases hx : (Packets.deviceStore d).slots i with
    | none => simp [hx] at old
    | some n =>
      simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at old
      change stamp ≤ e.nextSkb
      rw [hn, ← old.2]; exact hi.packetBounded d hd i n hx
  · intro e hv
    obtain ⟨d, hd, he, _, _, _⟩ := hg.device hv
    rw [he, hne]; exact hi.epochBounded d hd
  · intro stamp hs
    rw [hne]; exact hi.packetPastEpoch stamp (hpacket ▸ hs)
  · intro e hv stamp hs
    obtain ⟨d, hd, he, _, hn, _⟩ := hg.device hv
    rw [hn]
    exact hi.packetPast d hd stamp (he ▸ (hpacket ▸ hs))

def peerCreateMixed (key : Key) (psk : Option Key) : MixedM (Except Int PeerId) :=
  peerFocus (Peers.peerCreatePrefix key psk)

theorem peerCreateMixed_erases (key : Key) (psk : Option Key) :
    ErasesPrefix (peerCreateMixed key psk) (peerCreate key psk) :=
  peerFocus_erases (Peers.peerCreatePrefix_erases key psk)

theorem peerCreateMixed_preserves (key : Key) (psk : Option Key) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (peerCreateMixed key psk) := by
  intro w h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := Peers.peerCreatePrefix_preserves key psk w
    (h.filterMap LifetimeEvent.peer?) hi.peer
  have hr : runPrefix (Peers.peerCreatePrefix key psk) w (h.filterMap LifetimeEvent.peer?) =
      ((runPrefix (Peers.peerCreatePrefix key psk) w (h.filterMap LifetimeEvent.peer?)).1,
        h.filterMap LifetimeEvent.peer? ++ suffix) := Prod.ext rfl hsuf
  unfold peerCreateMixed peerFocus
  rw [focusPrefix_suffix _ _ _ _ _ _ _ hr]
  have hp : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.peer? =
      h.filterMap LifetimeEvent.peer? ++ suffix := by
    rw [List.filterMap_append, filterMap_encoded LifetimeEvent.peer LifetimeEvent.peer? (fun _ => rfl)]
  have hk : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.keypair? =
      h.filterMap LifetimeEvent.keypair? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  have ht : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.packet? =
      h.filterMap LifetimeEvent.packet? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  refine ⟨suffix.map LifetimeEvent.peer, rfl, ?_, ?_⟩
  · exact ⟨by simpa only [hp, hsuf] using hsafe,
      hk ▸ hi.release.1.keypair.1, ht ▸ hi.release.1.packet.1⟩
  · cases ho : (runPrefix (Peers.peerCreatePrefix key psk) w (h.filterMap LifetimeEvent.peer?)).1 with
    | error e => trivial
    | ok out =>
      have original := (Peers.peerCreatePrefix_erases key psk w _).symm.trans ho
      exact hi.peerTransport (peerCreate_geometry key psk w out.2 out.1 original)
        (by simpa only [hp, hsuf, ho] using hout)
        (peerCreate_peerSlots key psk w out.2 out.1 hi.peerSlots original) hk ht

end Leanux.Proofs.WG.Lifetimes
