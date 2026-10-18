import Leanux.Proofs.WG.Lifetimes.ReleaseAmbient

/-! Allocation frontiers strengthen release safety without changing the older
access contracts. Slot frontiers and lifetime frontiers are separate: both peer
and keypair destinations must be vacant. Packet identities share one frontier
within a device epoch; earlier epochs are bounded by netIfindexNext. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def keyStore (w : WGWorld) : Store KeypairId := ⟨w.keypairCounter, keypairResidents w⟩

structure AllocationInv (h : List LifetimeEvent) (w : WGWorld) : Prop where
  release : ReleaseInv h w
  peer : Peers.CreationInv (h.filterMap LifetimeEvent.peer?) w
  peerSlots : ∀ d, w.dev = some d → ∀ i p, d.peers[i]? = some p → i < d.nextPeer
  keyBounded : Bounded (keyStore w)
  keyPast : ∀ stamp, AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) stamp →
    stamp ≤ w.keypairCounter
  keySlots : ∀ d, w.dev = some d → ∀ i k, d.keypairs[i]? = some k → i < d.nextKeypairId
  packetBounded : ∀ d, w.dev = some d → Bounded (Packets.deviceStore d)
  epochBounded : ∀ d, w.dev = some d → d.ifindex < w.netIfindexNext
  packetPastEpoch : ∀ stamp, AccessEvent.Released (h.filterMap LifetimeEvent.packet?) stamp →
    stamp.1 < w.netIfindexNext
  packetPast : ∀ d, w.dev = some d → ∀ stamp,
    AccessEvent.Released (h.filterMap LifetimeEvent.packet?) (d.ifindex, stamp) → stamp ≤ d.nextSkb

theorem AllocationInv.safe (hi : AllocationInv h w) : LifetimeEvent.Safe h := hi.release.safe

theorem AllocationInv.store (hi : AllocationInv h w)
    (he : wgStoreView v = wgStoreView w) : AllocationInv h v := by
  have hd := congrArg WGStoreView.dev he
  have hp := congrArg WGStoreView.peerCounter he
  have hk := congrArg WGStoreView.keypairCounter he
  have hn := congrArg WGStoreView.netIfindexNext he
  simp only [wgStoreView] at hd hp hk hn
  rcases hi with ⟨hr, hc, hps, hkb, hkp, hks, hpb, heb, hpe, hpp⟩
  have hv : identityView v = identityView w := by
    unfold identityView Peers.snapshot keypairResidents packetResidents
    rw [hd, hp]
  have hs : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst hv
  refine ⟨⟨hr.1.congr hv, hv ▸ hr.2⟩, hc.congr hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hd] using hps
  · unfold Bounded keyStore keypairResidents
    rw [hd, hk]
    exact hkb
  · simpa only [hk] using hkp
  · simpa only [hd] using hks
  · simpa only [hd] using hpb
  · simpa only [hd, hn] using heb
  · simpa only [hn] using hpe
  · simpa only [hd] using hpp

/-- Arbitrary actual-state actions, including product runner actions, retain
the allocation invariant when their projected WG store is unchanged. -/
theorem allocation_store {S : Type} (project : S → WGWorld)
    (a : StateT S (Except Stop) α)
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    PrefixPreserves (fun h w => AllocationInv h (project w)) LifetimeEvent.Safe (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ hi => hi.safe)
    (fun _ w x v hi hr => hi.store ((ProjectedAction.iff_run _ _ _).mp ha w x v hr))).preserves

theorem allocation_state_store (a : WG.M α) (ha : SameWGStore a) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi.safe)
    (fun _ w ambient x v ambient' hi hr => hi.store
      ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr))

theorem AllocationInv.key_vacant (hi : AllocationInv h w) (hd : w.dev = some d) :
    d.keypairs[d.nextKeypairId]? = none := by
  cases hk : d.keypairs[d.nextKeypairId]? with
  | none => rfl
  | some k => exact False.elim (Nat.lt_irrefl _ (hi.keySlots d hd _ _ hk))

theorem AllocationInv.peer_vacant (hi : AllocationInv h w) (hd : w.dev = some d) :
    d.peers[d.nextPeer]? = none := by
  cases hp : d.peers[d.nextPeer]? with
  | none => rfl
  | some p => exact False.elim (Nat.lt_irrefl _ (hi.peerSlots d hd _ _ hp))

theorem AllocationInv.packet_vacant (hi : AllocationInv h w) (hd : w.dev = some d) :
    d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none :=
  Packets.allocation_slots_empty w d hd (by simpa [Packets.Inv, Packets.snapshot, hd] using hi.packetBounded d hd)

def insertResident [DecidableEq ι] (r : ι → Option κ) (i : ι) (stamp : κ) :=
  fun j => if j = i then some stamp else r j

theorem ResidentUnique.insert {r : ι → Option κ} {i : ι} {stamp : κ}
    [DecidableEq ι] (hu : ResidentUnique r)
    (hf : ∀ j, r j ≠ some stamp) : ResidentUnique (insertResident r i stamp) := by
  intro j k s hj hk
  by_cases hji : j = i <;> by_cases hki : k = i
  · exact hji.trans hki.symm
  · simp [insertResident, hji] at hj
    subst s
    exact False.elim (hf k (by simpa [insertResident, hki] using hk))
  · simp [insertResident, hki] at hk
    subst s
    exact False.elim (hf j (by simpa [insertResident, hji] using hj))
  · exact hu j k s (by simpa [insertResident, hji] using hj)
      (by simpa [insertResident, hki] using hk)

theorem ResidentSafe.allocate {r : ι → Option κ} {i : ι} {stamp : κ}
    [DecidableEq ι] (hi : ResidentSafe h r)
    (hf : ¬ AccessEvent.Released h stamp) :
    ResidentSafe (h ++ [.allocate i stamp, .write i stamp]) (insertResident r i stamp) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      AccessEvent.safe_append_write (slot := i)
        (AccessEvent.safe_append_allocate (slot := i) hi.1 hf)
        (by simpa only [AccessEvent.released_append_allocate] using hf)
  · intro s hs j hj
    have old : AccessEvent.Released h s := by simpa [AccessEvent.Released] using hs
    by_cases he : j = i
    · simp [insertResident, he] at hj
      subst s
      exact hf old
    · exact hi.2 s old j (by simpa [insertResident, he] using hj)

end Leanux.Proofs.WG.Lifetimes
