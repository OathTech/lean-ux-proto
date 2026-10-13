import Leanux.Proofs.WG.Peers.Frames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Atomic allocation refinement for the original peer creation function.
The counter increment and insertion are proved together: their intermediate
state is not itself a lifetime transition. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

theorem mapStore_allocate (frontier : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (p : Peer) (hp : p.internalId = frontier + 1) :
    mapStore (frontier + 1) (peers.insert i p) = (mapStore frontier peers).allocate i := by
  apply Store.ext
  · rfl
  · funext j
    simp only [mapStore, Store.allocate, Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h : i = j <;> simp_all [eq_comm]

theorem peerCreate_spec (start : World) (publicKey : Key) (psk : Option Key) :
    ⦃fun w => ⌜w.k = start.k⌝⦄ peerCreate publicKey psk
    ⦃⇓? result w => ⌜snapshot w = match result with
      | .error _ => snapshot start
      | .ok pid => (snapshot start).allocate pid⌝⦄ := by
  have alloc_spec := sameKernel_wp _ (Keypairs.hiddenAlloc_sameKernel .kmemCacheZallocPeer)
    (fun k => k = start.k)
  have reset_spec := fun pid => (dstCacheReset_samePeerSnapshot pid).wp
    (fun s => s = (snapshot start).allocate pid)
  have handshake_spec := fun pid => (handshakeInit_samePeerSnapshot pid psk).wp
    (fun s => s = (snapshot start).allocate pid)
  have time_spec := fun pid => (resetLastSentHandshake_samePeerSnapshot pid).wp
    (fun s => s = (snapshot start).allocate pid)
  mvcgen [peerCreate, alloc_spec, reset_spec, handshake_spec, time_spec,
    getDev, getK, setPeer, modifyDev, modifyK, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot, Option.bind_map, Function.comp_def]
  exact mapStore_allocate _ _ _ _ rfl

/-- Exact refinement needs no well-formedness assumption about the old store.
In particular it does not assert that the old nextPeer slot was empty. -/
theorem peerCreate_exact (publicKey : Key) (psk : Option Key)
    (w w' : World) (result : Except Int PeerId)
    (hr : (peerCreate publicKey psk).run w = .ok (result, w')) :
    snapshot w' = match result with
      | .error _ => snapshot w
      | .ok pid => (snapshot w).allocate pid := by
  have he := (hoare_iff_triple _ _ _).mpr (peerCreate_spec w publicKey psk) w result w' rfl hr
  cases result <;> exact he

theorem peerCreate_transition (publicKey : Key) (psk : Option Key) :
    ProjectedAction snapshot Transition (peerCreate publicKey psk) := by
  intro w result w' hr
  rw [peerCreate_exact publicKey psk w w' result hr]
  cases result with
  | error _ => exact .refl _
  | ok pid => exact allocate_transition _ pid

theorem peerCreate_bounded (publicKey : Key) (psk : Option Key)
    (w w' : World) (result : Except Int PeerId)
    (hb : Bounded (snapshot w))
    (hr : (peerCreate publicKey psk).run w = .ok (result, w')) :
    Bounded (snapshot w') := by
  rw [peerCreate_exact publicKey psk w w' result hr]
  cases result with
  | error _ => exact hb
  | ok pid => exact allocate_bounded _ pid hb

theorem peerCreate_fresh (publicKey : Key) (psk : Option Key)
    (w w' : World) (pid : PeerId)
    (hr : (peerCreate publicKey psk).run w = .ok (.ok pid, w')) :
    (snapshot w').frontier = (snapshot w).frontier + 1 ∧
      (snapshot w').slots pid = some ((snapshot w).frontier + 1) := by
  rw [peerCreate_exact publicKey psk w w' (.ok pid) hr]
  simp [Store.allocate]

/-- Actual lookup, reference acquisition/release, and atomic creation. A raw
unconditional setter is excluded: its use requires the separate live contract. -/
inductive Operation : (α : Type) → M α → Prop where
  | reference (h : Primitive α a) : Operation α a
  | acquireMaybe (peer : Option PeerId) :
      Operation (Option PeerId) (peerGetMaybeZero peer)
  | create (publicKey : Key) (psk : Option Key) :
      Operation (Except Int PeerId) (peerCreate publicKey psk)

theorem operation_contract (h : Operation α a) :
    Action (fun w => Bounded (snapshot w))
      (fun w v => Transition (snapshot w) (snapshot v)) a := by
  intro w result w' hb hr
  cases h with
  | reference hp =>
    have retained := (primitive_contract hp w result w' True.intro hr).2
    exact ⟨retained.bounded hb, retained.transition⟩
  | acquireMaybe peer =>
    dsimp only
    rw [peerGetMaybeZero_samePeerSnapshot peer w result w' hr]
    exact ⟨hb, .refl _⟩
  | create publicKey psk =>
    exact ⟨peerCreate_bounded publicKey psk w w' result hb hr,
      peerCreate_transition publicKey psk w result w' hr⟩

def AllocationSequence := Executions Operation

theorem allocation_sequence_contract (h : AllocationSequence w w')
    (hb : Bounded (snapshot w)) :
    Bounded (snapshot w') ∧ Transition (snapshot w) (snapshot w') :=
  h.contract (P := fun w => Bounded (snapshot w))
    (R := fun w v => Transition (snapshot w) (snapshot v))
    (fun w => Transition.refl (snapshot w)) (fun _ _ _ => Transition.trans)
    (fun _ hp => operation_contract hp) hb

end Leanux.Proofs.WG.Peers
