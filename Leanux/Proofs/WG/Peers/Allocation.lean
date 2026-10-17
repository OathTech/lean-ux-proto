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

theorem peerCreate_spec (start : WGWorld) (publicKey : Key) (psk : Option Key) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerCreate publicKey psk
    ⦃⇓? result w => ⌜snapshot w = match result with
      | .error _ => snapshot start
      | .ok pid => (snapshot start).allocate pid⌝⦄ := by

  let core (pid : PeerId) : WG.M Unit := do
    let internalId := (← get).peerCounter + 1
    modify fun k => { k with peerCounter := internalId }
    modifyDev fun d => { d with nextPeer := pid + 1 }
    setPeer pid { remoteStatic := publicKey, presharedKey := List.replicate 32 0, precomputedStaticStatic := List.replicate 32 0, internalId, cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey), cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey) }
  let tail (pid : PeerId) : WG.M (Except Int PeerId) := do
    dstCacheReset pid
    handshakeInit pid psk
    resetLastSentHandshake pid
    modifyDev fun d => {d with peerList := d.peerList ++ [pid], peerHashtable := (publicKey, pid) :: d.peerHashtable, numPeers := d.numPeers + 1}
    return .ok pid
  have source : peerCreate publicKey psk = (do
      let d ← getDev
      if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
          d.numPeers MAX_PEERS_PER_DEVICE then return .error (-ENOMEM)
      if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then
        return .error (-ENOMEM)
      if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
      core d.nextPeer
      tail d.nextPeer) := by
    simp only [peerCreate, core, tail, bind_assoc]
  let P := fun w : WGWorld => wgStoreView w = wgStoreView start
  let Q := fun (result : Except Int PeerId) (w : WGWorld) =>
    snapshot w = match result with
      | .error _ => snapshot start
      | .ok pid => (snapshot start).allocate pid
  have snapshot_eq (w : WGWorld) (h : P w) : snapshot w = snapshot start :=
    congrArg snapshotOfWGStoreView h
  have ambient {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (StateT.lift a) := hoare_liftAmbient a R
  have getter : Hoare getDev P (fun d w => P w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient d out ambient' hi hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some saved =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hi, hd⟩
  have fail (d : Device) : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId))
      (fun w => P w ∧ w.dev = some d) Q := by
    apply hoare_consequence (hoare_pure (Except.error (-ENOMEM) : Except Int PeerId) _)
    · intro _ h; exact h
    · intro result w h
      rcases h with ⟨rfl, h⟩
      exact snapshot_eq w h.1
  have core_spec (pid : PeerId) (d : Device) :
      Hoare (core pid) (fun w => P w ∧ w.dev = some d)
        (fun _ w => snapshot w = (snapshot start).allocate pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient u out ambient' hi hr
    simp [core, setPeer, modifyDev, hi.2] at hr
    rcases hr with ⟨rfl, rfl⟩
    rw [← snapshot_eq w hi.1]
    simpa [snapshot, hi.2, mapStore] using
      mapStore_allocate w.peerCounter d.peers pid
        {remoteStatic := publicKey, presharedKey := List.replicate 32 0, precomputedStaticStatic := List.replicate 32 0, internalId := w.peerCounter + 1, cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey), cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey)} rfl
  have tail_spec (pid : PeerId) : Hoare (tail pid)
      (fun w => snapshot w = (snapshot start).allocate pid) Q := by
    unfold tail
    apply hoare_bind _ _ (SameView.wp (dstCacheReset_samePeerSnapshot pid)
      (fun t => t = (snapshot start).allocate pid))
    intro _
    apply hoare_bind _ _ (SameView.wp (handshakeInit_samePeerSnapshot pid psk)
      (fun t => t = (snapshot start).allocate pid))
    intro _
    apply hoare_bind _ _ (SameView.wp (resetLastSentHandshake_samePeerSnapshot pid)
      (fun t => t = (snapshot start).allocate pid))
    intro _
    apply hoare_bind _ _ (modifyDev_peer_spec (fun t => t = (snapshot start).allocate pid)
      (fun d => {d with peerList := d.peerList ++ [pid], peerHashtable := (publicKey, pid) :: d.peerHashtable, numPeers := d.numPeers + 1})
      (fun _ => rfl))
    intro _
    apply hoare_consequence (hoare_pure (Except.ok pid : Except Int PeerId) _)
    · intro _ h; exact h
    · intro result w h
      rcases h with ⟨rfl, h⟩
      exact h
  rw [source]
  apply hoare_bind _ _ getter
  intro d
  apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)
    (fun w => P w ∧ w.dev = some d))
  intro maxPeers
  cases maxPeers with
  | true => exact fail d
  | false =>
    apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
      (fun w => P w ∧ w.dev = some d))
    intro allocated
    apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated)
      (fun w => P w ∧ w.dev = some d))
    intro noMem
    cases noMem with
    | true => exact fail d
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false)
        (fun w => P w ∧ w.dev = some d))
      intro cacheFailed
      cases cacheFailed with
      | true => exact fail d
      | false =>
        exact hoare_bind _ _ (core_spec d.nextPeer d) (fun _ => tail_spec d.nextPeer)

/-- Exact refinement needs no well-formedness assumption about the old store.
In particular it does not assert that the old nextPeer slot was empty. -/
theorem peerCreate_exact (publicKey : Key) (psk : Option Key)
    (w w' : WGWorld) (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate publicKey psk).run w).run ambient = .ok ((result, w'), ambient')) :
    snapshot w' = match result with
      | .error _ => snapshot w
      | .ok pid => (snapshot w).allocate pid := by
  have he := (hoare_iff_run_ambient _ _ _).mp (peerCreate_spec w publicKey psk)
    w ambient result w' ambient' rfl hr
  cases result <;> exact he

theorem peerCreate_transition (publicKey : Key) (psk : Option Key) :
    ProjectedAction snapshot Transition (peerCreate publicKey psk) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result w' ambient' hr
  rw [peerCreate_exact publicKey psk w w' result ambient ambient' hr]
  cases result with
  | error _ => exact .refl _
  | ok pid => exact allocate_transition _ pid

theorem peerCreate_bounded (publicKey : Key) (psk : Option Key)
    (w w' : WGWorld) (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hb : Bounded (snapshot w))
    (hr : ((peerCreate publicKey psk).run w).run ambient = .ok ((result, w'), ambient')) :
    Bounded (snapshot w') := by
  rw [peerCreate_exact publicKey psk w w' result ambient ambient' hr]
  cases result with
  | error _ => exact hb
  | ok pid => exact allocate_bounded _ pid hb

theorem peerCreate_fresh (publicKey : Key) (psk : Option Key)
    (w w' : WGWorld) (pid : PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate publicKey psk).run w).run ambient = .ok ((.ok pid, w'), ambient')) :
    (snapshot w').frontier = (snapshot w).frontier + 1 ∧
      (snapshot w').slots pid = some ((snapshot w).frontier + 1) := by
  rw [peerCreate_exact publicKey psk w w' (.ok pid) ambient ambient' hr]
  simp [Store.allocate]

/-- Actual lookup, reference acquisition/release, and atomic creation. A raw
unconditional setter is excluded: its use requires the separate live contract. -/
inductive Operation : (α : Type) → WG.M α → Prop where
  | reference (h : Primitive α a) : Operation α a
  | acquireMaybe (peer : Option PeerId) :
      Operation (Option PeerId) (peerGetMaybeZero peer)
  | create (publicKey : Key) (psk : Option Key) :
      Operation (Except Int PeerId) (peerCreate publicKey psk)

theorem operation_contract (h : Operation α a) :
    Action (fun w => Bounded (snapshot w))
      (fun w v => Transition (snapshot w) (snapshot v)) a := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient result w' ambient' hb hr
  cases h with
  | reference hp =>
    have retained := ((Action.iff_run_ambient _ _ _).mp (primitive_contract hp)
      w ambient result w' ambient' True.intro hr).2
    exact ⟨retained.bounded hb, retained.transition⟩
  | acquireMaybe peer =>
    rw [(ProjectedAction.iff_run_ambient _ _ _).mp (peerGetMaybeZero_samePeerSnapshot peer)
      w ambient result w' ambient' hr]
    exact ⟨hb, .refl _⟩
  | create publicKey psk =>
    exact ⟨peerCreate_bounded publicKey psk w w' result ambient ambient' hb hr,
      (ProjectedAction.iff_run_ambient _ _ _).mp (peerCreate_transition publicKey psk)
        w ambient result w' ambient' hr⟩

def AllocationSequence := Executions Operation

theorem allocation_sequence_contract (h : AllocationSequence w ambient w' ambient')
    (hb : Bounded (snapshot w)) :
    Bounded (snapshot w') ∧ Transition (snapshot w) (snapshot w') :=
  h.contract (P := fun w => Bounded (snapshot w))
    (R := fun w v => Transition (snapshot w) (snapshot v))
    (fun w => Transition.refl (snapshot w)) (fun _ _ _ => Transition.trans)
    (fun _ hp => operation_contract hp) hb

end Leanux.Proofs.WG.Peers
