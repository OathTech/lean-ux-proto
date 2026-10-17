import Leanux.Proofs.WG.Lifetimes.AllocationAmbient
import Leanux.Proofs.WG.Peers.Allocation

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Successful-state geometry of the original peer creation call. The existing
peer-snapshot theorem supplies its identity transition; these frames add the
other lifetime families and allocation cursors without changing observers. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def peerInitView (w : WGWorld) := (otherResidents w, allocationMetadata w)

theorem peerInit_sameWGStore
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => peerInitView (project s)) a := by
  have residents := (identity_sameWGStore ha).factor (fun s : IdentityView => s.2)
  have metadata := ha.of_factor
    (fun s : WGStoreView => (⟨s.keypairCounter, s.netIfindexNext,
      s.dev.map deviceAllocationMetadata⟩ : AllocationMetadata))
    (fun s => allocationMetadata (project s)) (fun _ => rfl)
  exact residents.product metadata

theorem dstCacheReset_peerInitView (pid : PeerId) : SameView peerInitView (dstCacheReset pid) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => peerInitView w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have device : Preserves P getDev :=
    (peerInit_sameWGStore (project := id) getDev_sameWGStore).wp (fun view => view = initial)
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' h hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact h
  have write (pid : PeerId) (p : Peer) : Preserves P (setPeer pid p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    unfold P peerInitView otherResidents keypairResidents packetResidents allocationMetadata at h ⊢
    cases hd : w.dev <;> simpa [deviceAllocationMetadata, hd] using h
  change Preserves P (dstCacheReset pid)
  unfold dstCacheReset
  simp (config := { zeta := true }) only
    [hiddenJiffies, getAmbient]
  repeat' first
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head getDev; exact device)
    | (allocation_release_head setPeer; exact write _ _)
    | (allocation_release_head get; exact hoare_consequence (hoare_get P)
        (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem resetLastSentHandshake_peerInitView (pid : PeerId) :
    SameView peerInitView (resetLastSentHandshake pid) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => peerInitView w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have device : Preserves P getDev :=
    (peerInit_sameWGStore (project := id) getDev_sameWGStore).wp (fun view => view = initial)
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' h hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact h
  have write (pid : PeerId) (p : Peer) : Preserves P (setPeer pid p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    unfold P peerInitView otherResidents keypairResidents packetResidents allocationMetadata at h ⊢
    cases hd : w.dev <;> simpa [deviceAllocationMetadata, hd] using h
  change Preserves P (resetLastSentHandshake pid)
  unfold resetLastSentHandshake
  simp (config := { zeta := true }) only
    [hiddenClock64]
  repeat' first
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head getDev; exact device)
    | (allocation_release_head setPeer; exact write _ _)
    | (allocation_release_head get; exact hoare_consequence (hoare_get P)
        (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem precomputeStaticStatic_peerInitView (pid : PeerId) :
    SameView peerInitView (precomputeStaticStatic pid) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => peerInitView w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have device : Preserves P getDev :=
    (peerInit_sameWGStore (project := id) getDev_sameWGStore).wp (fun view => view = initial)
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' h hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact h
  have write (pid : PeerId) (p : Peer) : Preserves P (setPeer pid p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    unfold P peerInitView otherResidents keypairResidents packetResidents allocationMetadata at h ⊢
    cases hd : w.dev <;> simpa [deviceAllocationMetadata, hd] using h
  change Preserves P (precomputeStaticStatic pid)
  unfold precomputeStaticStatic
  simp (config := { zeta := true }) only
    [requireNotPending, branch]
  repeat' first
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head getDev; exact device)
    | (allocation_release_head setPeer; exact write _ _)
    | (allocation_release_head get; exact hoare_consequence (hoare_get P)
        (fun _ h => h) (fun _ _ h => h.2))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem handshakeInit_peerInitView (pid : PeerId) (psk : Option Key) :
    SameView peerInitView (handshakeInit pid psk) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => peerInitView w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have device : Preserves P getDev :=
    (peerInit_sameWGStore (project := id) getDev_sameWGStore).wp (fun view => view = initial)
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' h hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact h
  have write (pid : PeerId) (p : Peer) : Preserves P (setPeer pid p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    unfold P peerInitView otherResidents keypairResidents packetResidents allocationMetadata at h ⊢
    cases hd : w.dev <;> simpa [deviceAllocationMetadata, hd] using h
  change Preserves P (handshakeInit pid psk)
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := { zeta := true }) only [branch]
  repeat' first
    | (allocation_release_head getPeer; exact read _)
    | (allocation_release_head setPeer; exact write _ _)
    | (allocation_release_head precomputeStaticStatic;
        exact (precomputeStaticStatic_peerInitView _).wp (fun view => view = initial))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

def peerCreateMetadata (m : AllocationMetadata) : Except Int PeerId → AllocationMetadata
  | .error _ => m
  | .ok pid => {m with device := m.device.map fun d => {d with nextPeer := pid + 1}}

def PeerCreationGeometry (w : WGWorld) (result : Except Int PeerId) (v : WGWorld) : Prop :=
  otherResidents v = otherResidents w ∧
  allocationMetadata v = peerCreateMetadata (allocationMetadata w) result ∧
  match result with
  | .error _ => True
  | .ok pid => w.dev.map (·.nextPeer) = some pid

theorem peerCreate_geometry_wp (start : WGWorld) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜PeerCreationGeometry start result w⌝⦄ := by
  let P := fun w : WGWorld => wgStoreView w = wgStoreView start
  let I := fun pid (w : WGWorld) =>
    otherResidents w = otherResidents start ∧
    allocationMetadata w = peerCreateMetadata (allocationMetadata start) (.ok pid) ∧
    start.dev.map (·.nextPeer) = some pid
  let after := fun pid (s : ((KeypairId → Option Nat) × (Packets.Slot → Option PacketStamp)) × AllocationMetadata) =>
    s.1 = otherResidents start ∧
    s.2 = peerCreateMetadata (allocationMetadata start) (.ok pid) ∧
    start.dev.map (·.nextPeer) = some pid
  have read : Hoare getDev P (fun d w => P w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v a' h hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some device =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨h, hd⟩
  have failure (code : Int) :
      Hoare (pure (.error code) : WG.M (Except Int PeerId)) P (PeerCreationGeometry start) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v a' h hr
    cases hr
    have hv : peerInitView w = peerInitView start := by
      have hd := congrArg WGStoreView.dev h
      have hk := congrArg WGStoreView.keypairCounter h
      have hn := congrArg WGStoreView.netIfindexNext h
      dsimp only [wgStoreView] at hd hk hn
      unfold peerInitView otherResidents keypairResidents packetResidents allocationMetadata
      simp only [hd, hk, hn]
    exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv, trivial⟩
  let prepare (d : Device) : WG.M Unit := do
    let pid := d.nextPeer
    let internalId := (← get).peerCounter + 1
    modify fun k => { k with peerCounter := internalId }
    modifyDev fun d => { d with nextPeer := pid + 1 }
    setPeer pid {
      remoteStatic := key, presharedKey := List.replicate 32 0,
      precomputedStaticStatic := List.replicate 32 0, internalId,
      cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ key),
      cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ key) }
  have prepareSpec (d : Device) :
      Hoare (prepare d) (fun w => P w ∧ w.dev = some d) (fun _ => I d.nextPeer) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    have hd := congrArg WGStoreView.dev h.1
    have hk := congrArg WGStoreView.keypairCounter h.1
    have hn := congrArg WGStoreView.netIfindexNext h.1
    dsimp only [wgStoreView] at hd hk hn
    unfold I otherResidents keypairResidents packetResidents allocationMetadata peerCreateMetadata
    simp [deviceAllocationMetadata, h.2, ← hd, ← hk, ← hn]
  have finishSpec (pid : PeerId) :
      Preserves (I pid) (modifyDev fun d => { d with
        peerList := d.peerList ++ [pid],
        peerHashtable := (key, pid) :: d.peerHashtable,
        numPeers := d.numPeers + 1 }) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    cases hr
    unfold I otherResidents keypairResidents packetResidents allocationMetadata at h ⊢
    cases hd : w.dev <;> simpa [hd, deviceAllocationMetadata] using h
  let finish (pid : PeerId) : WG.M (Except Int PeerId) := do
    dstCacheReset pid
    handshakeInit pid psk
    resetLastSentHandshake pid
    modifyDev fun d => { d with
      peerList := d.peerList ++ [pid],
      peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 }
    return .ok pid
  have finishSpec' (pid : PeerId) :
      Hoare (finish pid) (I pid) (PeerCreationGeometry start) := by
    unfold finish
    apply hoare_bind _ _ ((dstCacheReset_peerInitView pid).wp (after pid))
    intro _
    apply hoare_bind _ _ ((handshakeInit_peerInitView pid psk).wp (after pid))
    intro _
    apply hoare_bind _ _ ((resetLastSentHandshake_peerInitView pid).wp (after pid))
    intro _
    apply hoare_bind _ _ (finishSpec pid)
    intro _
    exact hoare_consequence (hoare_pure (Except.ok pid : Except Int PeerId) (I pid))
      (fun _ h => h) (fun _ _ h => by rcases h with ⟨rfl, h⟩; exact h)
  have source : peerCreate key psk = (do
      let d ← getDev
      if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
        return .error (-ENOMEM)
      if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then
        return .error (-ENOMEM)
      if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
      prepare d
      finish d.nextPeer) := by
    simp only [peerCreate, prepare, finish, bind_assoc]
  rw [source]
  apply hoare_bind _ _ read
  intro d
  let R := fun w : WGWorld => P w ∧ w.dev = some d
  have ambient {α : Type} (a : AmbientM α) :
      Preserves R (monadLift a : WG.M α) := hoare_liftAmbient a R
  have failed : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) R
      (PeerCreationGeometry start) :=
    hoare_consequence (failure _) (fun _ h => h.1) (fun _ _ h => h)
  apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
  intro full
  cases full with
  | true => exact failed
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
    intro allocated
    apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem (!allocated)))
    intro noMemory
    cases noMemory with
    | true => exact failed
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
      intro noCache
      cases noCache with
      | true => exact failed
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hoare_bind _ _ (prepareSpec d) (fun _ => finishSpec' d.nextPeer)

theorem peerCreate_geometry (key : Key) (psk : Option Key) (w v : WGWorld)
    (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    PeerCreationGeometry w result v :=
  (hoare_iff_run_ambient _ _ _).mp (peerCreate_geometry_wp w key psk)
    w ambient result v ambient' rfl hr

end Leanux.Proofs.WG.Lifetimes
