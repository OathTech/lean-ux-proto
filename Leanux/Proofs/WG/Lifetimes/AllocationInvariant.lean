import Leanux.Proofs.WG.Lifetimes.ReleaseAmbient

/-! Allocation frontiers strengthen release safety without changing the older
access contracts. Slot frontiers and lifetime frontiers are separate: both peer
and keypair destinations must be vacant. Packet identities share one frontier
within a device epoch; earlier epochs are bounded by netIfindexNext. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def keyStore (w : World) : Store KeypairId := ⟨w.k.keypairCounter, keypairResidents w⟩

structure AllocationInv (h : List LifetimeEvent) (w : World) : Prop where
  release : ReleaseInv h w
  peer : Peers.CreationInv (h.filterMap LifetimeEvent.peer?) w
  peerSlots : ∀ d, w.k.wg = some d → ∀ i p, d.peers[i]? = some p → i < d.nextPeer
  keyBounded : Bounded (keyStore w)
  keyPast : ∀ stamp, AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) stamp →
    stamp ≤ w.k.keypairCounter
  keySlots : ∀ d, w.k.wg = some d → ∀ i k, d.keypairs[i]? = some k → i < d.nextKeypairId
  packetBounded : ∀ d, w.k.wg = some d → Bounded (Packets.deviceStore d)
  epochBounded : ∀ d, w.k.wg = some d → d.ifindex < w.k.netIfindexNext
  packetPastEpoch : ∀ stamp, AccessEvent.Released (h.filterMap LifetimeEvent.packet?) stamp →
    stamp.1 < w.k.netIfindexNext
  packetPast : ∀ d, w.k.wg = some d → ∀ stamp,
    AccessEvent.Released (h.filterMap LifetimeEvent.packet?) (d.ifindex, stamp) → stamp ≤ d.nextSkb

theorem AllocationInv.safe (hi : AllocationInv h w) : LifetimeEvent.Safe h := hi.release.safe

theorem AllocationInv.kernel (hi : AllocationInv h w) (he : v.k = w.k) : AllocationInv h v := by
  rcases hi with ⟨hr, hp, hps, hkb, hkp, hks, hpb, heb, hpe, hpp⟩
  have hv : identityView v = identityView w := by
    unfold identityView Peers.snapshot keypairResidents packetResidents
    rw [he]
  have hs : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst hv
  refine ⟨⟨hr.1.congr hv, hv ▸ hr.2⟩, hp.congr hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using hps
  · unfold Bounded keyStore keypairResidents
    rw [he]
    exact hkb
  · simpa only [he] using hkp
  · simpa only [he] using hks
  · simpa only [he] using hpb
  · simpa only [he] using heb
  · simpa only [he] using hpe
  · simpa only [he] using hpp

theorem allocation_kernel (a : M α) (ha : SameKernel a) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ hi => hi.safe)
    (fun _ _ _ _ hi hr => hi.kernel (ha _ _ _ hr))).preserves

theorem AllocationInv.key_vacant (hi : AllocationInv h w) (hd : w.k.wg = some d) :
    d.keypairs[d.nextKeypairId]? = none := by
  cases hk : d.keypairs[d.nextKeypairId]? with
  | none => rfl
  | some k => exact False.elim (Nat.lt_irrefl _ (hi.keySlots d hd _ _ hk))

theorem AllocationInv.peer_vacant (hi : AllocationInv h w) (hd : w.k.wg = some d) :
    d.peers[d.nextPeer]? = none := by
  cases hp : d.peers[d.nextPeer]? with
  | none => rfl
  | some p => exact False.elim (Nat.lt_irrefl _ (hi.peerSlots d hd _ _ hp))

theorem AllocationInv.packet_vacant (hi : AllocationInv h w) (hd : w.k.wg = some d) :
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
