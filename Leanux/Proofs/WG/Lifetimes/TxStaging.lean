import Leanux.Proofs.WG.Lifetimes.TxEnqueue
import Leanux.Proofs.Framing.WGReceiveHeaders

set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-! Complete staged-send and keepalive callers. Staged Packet values are local
payloads; only their later newTxSkb calls allocate resident packet identities.
The no-key restoration deliberately retains both original peer getters. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem ipTunnelEcnEncap_sameWGWorld (pkt : Packet) :
    SameView (id : WGWorld → WGWorld) (ipTunnelEcnEncap pkt) := by
  have ambient {α : Type} (a : AmbientM α) :
      SameView (id : WGWorld → WGWorld) (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => w = initial)
  have protocol : SameView (id : WGWorld → WGWorld) pkt.protocol := by
    unfold Packet.protocol
    cases pkt.bytes with
    | nil =>
      simp only
      exact SameView.pure _ _
    | cons b rest =>
      simp only
      split
      · exact SameView.pure _ _
      · split
        · exact SameView.pure _ _
        · exact ambient (AmbientM.invariant "a staged packet that is neither empty nor IP")
  unfold ipTunnelEcnEncap
  apply SameView.bind protocol
  intro protocol
  apply SameView.bind (ipTunnelGetDsfield_sameWGWorld protocol pkt.bytes)
  intro inner
  apply SameView.bind (ambient (AmbientM.branch .ecnEncapInnerCe (inner % 4 == 3)))
  intro ce
  split <;> exact SameView.pure _ _

def purgeStagedPacketsPrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  liftWGPrefix (modifyDev fun d => { d with txDropped := d.txDropped + p.staged.length })
  setPeerMixed pid { p with staged := [] }


def stagedOutNokeyPrefix (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId)
    (invalid : Bool) : MixedM Unit := do
  if invalid then
    let some id := keypair | liftWGPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    setKeypairPrefix id { k with sending := { k.sending with isValid := false } }
  keypairPutPrefix keypair false
  for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
  _ ← liftWGPrefix (branch .stagedOrphanWalk false)
  setPeerMixed pid { (← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged }
  sendQueuedHandshakeInitiationPrefix pid false

def stagedOutNokey (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId)
    (invalid : Bool) : WG.M Unit := do
  if invalid then
    let some id := keypair | invariant "unreachable"
    let k ← getKeypair id
    setKeypair id { k with sending := { k.sending with isValid := false } }
  keypairPut keypair false
  for _ in packets do _ ← branch .stagedOrphanWalk true
  _ ← branch .stagedOrphanWalk false
  setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }
  sendQueuedHandshakeInitiation pid false

def sendStagedPacketsPrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  let packets := p.staged
  setPeerMixed pid { p with staged := [] }
  let keypair ← keypairGetPrefix p.keypairCurrent
  let outNokey := stagedOutNokeyPrefix pid packets keypair
  if ← liftWGPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftWGPrefix (invariant "unreachable")
  let k ← getKeypairPrefix id
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  if ← liftWGPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let k ← getKeypairPrefix id
    let nonce := k.sendingCounter
    setKeypairPrefix id { k with sendingCounter := k.sendingCounter + 1 }
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then return ← outNokey true
    packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  peerGetMixed (← peerDerefPrefix (.keypair id))
  let item ← packetsCb.mapM newTxSkbPrefix
  createDataPrefix pid item


def sendKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .keepaliveStagedEmpty p.staged.isEmpty) then
    if ← liftWGPrefix (branch .keepaliveNoMem !(← liftWGPrefix (hiddenAlloc .keepaliveSkb))) then return
    setPeerMixed pid { p with staged := p.staged ++ [{ mtu := (← liftWGPrefix getDev).mtu }] }
  sendStagedPacketsPrefix pid


theorem purgeStagedPacketsPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (purgeStagedPacketsPrefix pid) (purgeStagedPackets pid) := by
  unfold purgeStagedPacketsPrefix purgeStagedPackets
  exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => setPeerMixed_erases _ _))

theorem purgeStagedPacketsPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (purgeStagedPacketsPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold purgeStagedPacketsPrefix
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply StatePrefixEnsures.bind (t.device (fun s => True ∧ s.1.slots pid = some p.internalId) (.dropped p.staged.length))
  intro _
  exact c.setPeer (fun _ => True) pid {p with staged := []}

theorem keypairUpdateThen_preserves (c : AmbientContracts I) (id : KeypairId)
    (f : Keypair → Keypair) (hf : ∀ k, (f k).internalId = k.internalId)
    (next : Keypair → MixedM α) (hn : ∀ k, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (next k)) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (do let k ← getKeypairPrefix id; setKeypairPrefix id (f k); next k) := by
  have hg : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getKeypairPrefix id)
      (fun k h w _ => I h w ∧ (identityView w).2.1 id = some k.internalId) :=
    (c.getKeypair (fun _ => True) id).consequence
      (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply StatePrefixEnsures.bind hg
  intro k
  apply StatePrefixEnsures.bind ((c.setKeypair (fun _ => True) id (f k)).consequence
    (fun _ _ _ hi => ⟨hi.1, True.intro, (hf k) ▸ hi.2⟩) (fun _ _ _ _ hi => hi.1))
  intro _
  exact hn k

theorem stagedRestore_preserves (c : AmbientContracts I) (pid : PeerId) (packets : List Packet) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (do setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged}) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply StatePrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := packets ++ q.staged}

theorem stagedOutNokeyPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (packets : List Packet) (kp : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (stagedOutNokeyPrefix pid packets kp invalid) := by
  have hq (pid) := AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  unfold stagedOutNokeyPrefix
  have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (do
        keypairPutPrefix kp false
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)
        setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged}
        sendQueuedHandshakeInitiationPrefix pid false) := by
    apply StatePrefixEnsures.bind (t.put _ _)
    intro _
    apply StatePrefixEnsures.bind (StatePrefixEnsures.forInInvariant packets () _
      (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi) (fun _ _ =>
        StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          (fun _ => StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))))
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    have hr := stagedRestore_preserves c pid packets
    simpa only [bind_assoc] using StatePrefixEnsures.bind hr (fun _ =>
      sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq pid false)
  cases invalid
  · exact tail
  · cases kp with
    | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | some id =>
      exact keypairUpdateThen_preserves c id
        (fun k => {k with sending := {k.sending with isValid := false}}) (fun _ => rfl)
        (fun _ => _) (fun _ => tail)

theorem stagedOutNokeyPrefix_erases (pid : PeerId) (packets : List Packet)
    (kp : Option KeypairId) (invalid : Bool) :
    ErasesStatePrefix (stagedOutNokeyPrefix pid packets kp invalid) (stagedOutNokey pid packets kp invalid) := by
  unfold stagedOutNokeyPrefix stagedOutNokey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact getKeypairPrefix_erases _
    | with_reducible exact setKeypairPrefix_erases _ _
    | with_reducible exact keypairPutPrefix_erases _ _
    | with_reducible exact sendQueuedHandshakeInitiationPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem sendStagedPacketsPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (sendStagedPacketsPrefix pid) (sendStagedPackets pid) := by
  have map_erase {α β : Type} (xs : List α) (g : α → MixedM β) (a : α → WG.M β)
      (ha : ∀ x, ErasesStatePrefix (g x) (a x)) :
      ErasesStatePrefix (xs.mapM g) (xs.mapM a) := by
    induction xs with
    | nil => exact erasesStatePrefix_pure _
    | cons x xs ih =>
      simp only [List.mapM_cons]
      exact erasesStatePrefix_bind (ha x) (fun y =>
        erasesStatePrefix_bind ih (fun ys => erasesStatePrefix_pure (y :: ys)))
  unfold sendStagedPacketsPrefix sendStagedPackets
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro empty
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (setPeerMixed_erases _ _)
    intro _
    apply erasesStatePrefix_bind (keypairGetPrefix_erases _)
    intro kp
    have hout (invalid : Bool) := stagedOutNokeyPrefix_erases pid p.staged kp invalid
    change ErasesStatePrefix
      (do
        if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then return ← stagedOutNokeyPrefix pid p.staged kp false
        _) _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        apply erasesStatePrefix_bind (getKeypairPrefix_erases _)
        intro k
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro invalid
        split
        · exact hout false
        · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro expired
          split
          · exact hout true
          · repeat' first
              | with_reducible exact peerDerefPrefix_erases _
              | with_reducible exact getKeypairPrefix_erases _
              | with_reducible exact setKeypairPrefix_erases _ _
              | with_reducible exact peerGetMixed_erases _
              | with_reducible exact createDataPrefix_erases _ _
              | with_reducible exact PacketAllocation.erases (.tx _)
              | exact erasesStatePrefix_lift _
              | with_reducible exact erasesStatePrefix_pure _
              | exact hout true
              | with_reducible apply map_erase
              | with_reducible apply erasesStatePrefix_forIn
              | with_reducible apply erasesStatePrefix_bind
              | split
              | (solve | simp_all only)
              | (with_reducible intro x; try dsimp only)
            all_goals first
              | exact PacketAllocation.erases (.tx _)
              | (solve | simp_all)
              | (simp_all only [Option.some.injEq]; exact hout true)

theorem sendStagedPacketsPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendStagedPacketsPrefix pid) := by
  have map_preserves {α β : Type} (xs : List α) (g : α → MixedM β)
      (hg : ∀ x, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (g x)) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (xs.mapM g) := by
    induction xs with
    | nil => exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | cons x xs ih =>
      simp only [List.mapM_cons]
      exact StatePrefixEnsures.bind (hg x) (fun y => StatePrefixEnsures.bind ih (fun ys =>
        StatePrefixEnsures.pure (y :: ys) (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)))
  have loop_preserves {α β : Type} (xs : List α) (b : β)
      (g : α → β → MixedM (ForInStep β))
      (hg : ∀ x b, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (g x b)) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (forIn xs b g) :=
    StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => I h w) LifetimeEvent.Safe
      (fun _ h w _ hi => c.safe h w hi) hg
  have hq (pid) := AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  unfold sendStagedPacketsPrefix
  have hg : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w _ => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply StatePrefixEnsures.bind hg
  intro p
  apply StatePrefixEnsures.bind (c.branch (fun s => s.1.slots pid = some p.internalId) _ _)
  intro empty
  split
  · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi.1) (fun _ _ _ hi => hi.1)
  · apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := []}).consequence
      (fun _ _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ _ hi => hi.1))
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (keypairGetPrefix_spec_ambient c (fun _ => True) p.keypairCurrent))
    intro kp
    have hout := stagedOutNokeyPrefix_preserves_ambient c t pid p.staged kp
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some id =>
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
        intro k
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro invalid
        split
        · exact hout false
        · apply StatePrefixEnsures.bind (AmbientContracts.drop
            (c.store (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
          intro expired
          split
          · exact hout true
          · repeat' first
              | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _)
              | with_reducible exact AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _)
              | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
              | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
              | exact AmbientContracts.drop (c.store (fun _ => True) _ ((ipTunnelEcnEncap_sameWGWorld _).factor wgStoreView))
              | with_reducible exact c.peerGet _
              | with_reducible exact t.alloc _
              | with_reducible exact createDataPrefix_preserves_ambient c t _ _
              | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
              | exact hout true
              | apply keypairUpdateThen_preserves c id (fun k => {k with sendingCounter := k.sendingCounter + 1}) (fun _ => rfl)
              | with_reducible apply map_preserves
              | with_reducible apply loop_preserves
              | with_reducible apply StatePrefixEnsures.bind
              | split
              | (with_reducible intro x; try dsimp only)

theorem sendKeepalivePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (sendKeepalivePrefix pid) (sendKeepalive pid) := by
  unfold sendKeepalivePrefix sendKeepalive
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem sendKeepalivePrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendKeepalivePrefix pid) := by
  unfold sendKeepalivePrefix
  have hg : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w _ => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply StatePrefixEnsures.bind hg
  intro p
  let P := fun s : IdentityView => s.1.slots pid = some p.internalId
  apply StatePrefixEnsures.bind (c.branch P _ _)
  intro empty
  split
  · apply StatePrefixEnsures.bind (c.store P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) (fun w => wgStoreView w = initial)))
    intro alloc
    apply StatePrefixEnsures.bind (c.branch P _ _)
    intro noMem
    split
    · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi.1) (fun _ _ _ hi => hi.1)
    · apply StatePrefixEnsures.bind (c.store P _ getDev_sameWGStore)
      intro d
      apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := p.staged ++ [{mtu := d.mtu}]}).consequence
        (fun _ _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ _ hi => hi.1))
      intro _
      exact sendStagedPacketsPrefix_preserves_ambient c t pid
  · exact StatePrefixEnsures.consequence (sendStagedPacketsPrefix_preserves_ambient c t pid)
      (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

theorem purgeStagedPacketsPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (purgeStagedPacketsPrefix pid)) := by
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  simp only [purgeStagedPacketsPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (t.device (fun s => True ∧ s.1.slots pid = some p.internalId) (.dropped p.staged.length))
  intro _
  exact c.setPeer (fun _ => True) pid {p with staged := []}


theorem keypairUpdateThen_preserves_product (c : ProductAmbientContracts I) (id : KeypairId)
    (f : Keypair → Keypair) (hf : ∀ k, (f k).internalId = k.internalId)
    (next : Keypair → PrefixM LifetimeEvent α) (hn : ∀ k, PrefixPreserves I LifetimeEvent.Safe (next k)) :
    PrefixPreserves I LifetimeEvent.Safe
      (do let k ← liftWGObserver (getKeypairPrefix id); liftWGObserver (setKeypairPrefix id (f k)); next k) := by
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getKeypairPrefix id))
      (fun k h w => I h w ∧ (identityView w.wg).2.1 id = some k.internalId) :=
    (c.getKeypair (fun _ => True) id).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro k
  apply PrefixEnsures.bind ((c.setKeypair (fun _ => True) id (f k)).consequence
    (fun _ _ hi => ⟨hi.1, True.intro, (hf k) ▸ hi.2⟩) (fun _ _ _ hi => hi.1))
  intro _
  exact hn k


theorem stagedRestore_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (packets : List Packet) :
    PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (do setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged})) := by
  simp only [liftWGObserver_bind]
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := packets ++ q.staged}


theorem stagedOutNokeyPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) (packets : List Packet) (kp : Option KeypairId) (invalid : Bool) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (stagedOutNokeyPrefix pid packets kp invalid)) := by
  have lift_loop {α β : Type} (xs : List α) (init : β)
      (f : α → β → MixedM (ForInStep β)) :
      liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
    induction xs generalizing init with
    | nil => simp only [List.forIn_nil, liftWGObserver_pure]
    | cons x xs ih =>
      simp only [List.forIn_cons, liftWGObserver_bind]
      congr 1
      funext step
      cases step with
      | done b => exact liftWGObserver_pure b
      | yield b => exact ih b
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  have hq (pid) := ProductAmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  simp only [stagedOutNokeyPrefix]
  have tail : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (do
        keypairPutPrefix kp false
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)
        setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged}
        sendQueuedHandshakeInitiationPrefix pid false)) := by
    simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
    apply PrefixPreserves.bind (t.put _ _)
    intro _
    apply PrefixPreserves.bind (PrefixPreserves.forIn _ _ _ c.safe (fun _ _ =>
      PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
        (fun _ => PrefixPreserves.pure c.safe _)))
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro _
    have hr := stagedRestore_preserves_product c pid packets
    simpa only [bind_assoc, liftWGObserver_bind] using PrefixPreserves.bind hr (fun _ =>
      sendQueuedHandshakeInitiationPrefix_preserves_product c hq pid false)
  cases invalid <;> simp only [Bool.false_eq_true, ite_false, ite_true, liftWGObserver_bind]
  · simpa only [liftWGObserver_bind] using tail
  · cases kp with
    | none => exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
    | some id =>
      simp only [liftWGObserver_bind]
      exact keypairUpdateThen_preserves_product c id
        (fun k => {k with sending := {k.sending with isValid := false}}) (fun _ => rfl)
        (fun _ => _) (fun _ => by simpa only [liftWGObserver_bind] using tail)


theorem sendStagedPacketsPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendStagedPacketsPrefix pid)) := by
  have lift_map {α β : Type} (xs : List α) (g : α → MixedM β) :
      liftWGObserver (xs.mapM g) = xs.mapM (fun x => liftWGObserver (g x)) := by
    induction xs with
    | nil => simp only [List.mapM_nil, liftWGObserver_pure]
    | cons x xs ih => simp only [List.mapM_cons, liftWGObserver_bind, liftWGObserver_pure, ih]
  have lift_loop {α β : Type} (xs : List α) (init : β)
      (f : α → β → MixedM (ForInStep β)) :
      liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
    induction xs generalizing init with
    | nil => simp only [List.forIn_nil, liftWGObserver_pure]
    | cons x xs ih =>
      simp only [List.forIn_cons, liftWGObserver_bind]
      congr 1
      funext step
      cases step with
      | done b => exact liftWGObserver_pure b
      | yield b => exact ih b
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  have branchCmp_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) (lhs rhs : Nat) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branchCmp d b lhs rhs))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branchCmp d b lhs rhs) (fun w => wgStoreView w = initial)
  have keyGet (P : IdentityView → Prop) (kp : Option KeypairId) :
      ProductAmbientSpec I P (liftWGObserver (keypairGetPrefix kp)) (fun _ => P) := by
    simp only [keypairGetPrefix, liftWGObserver_bind]
    apply PrefixEnsures.bind (branch_spec P _ _)
    intro isNull
    try simp only [liftWGObserver_pure, apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact c.pure P _
    · cases kp with
      | some id =>
        simp only [liftWGObserver_bind]
        apply PrefixEnsures.bind (c.getKeypair P id)
        intro k
        let Q := fun s : IdentityView => P s ∧ s.2.1 id = some k.internalId
        apply PrefixEnsures.bind (c.nativeStore Q _ (by
          have factor : (refcountIncNotZero k.refcount : WG.M Bool) =
              StateT.lift (refcountIncNotZero k.refcount : AmbientM Bool) := by
            change (refcountIncNotZero k.refcount : WG.M Bool) =
              (monadLift (refcountIncNotZero k.refcount : AmbientM Bool) : WG.M Bool)
            simp only [refcountIncNotZero, branch, branchCmp, unsupported, monadLift_self,
              monadLift_bind, monadLift_pure, apply_ite]
          rw [factor]
          intro initial
          exact hoare_liftAmbient (refcountIncNotZero k.refcount : AmbientM Bool)
            (fun w => wgStoreView w = initial)))
        intro nz
        apply PrefixEnsures.bind (branch_spec Q _ _)
        intro zero
        try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
        split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
        · exact ProductAmbientContracts.forget (c.pure Q none) (fun _ _ hi => hi.1)
        · try simp only [liftWGObserver_bind, liftWGObserver_pure]
          apply PrefixEnsures.bind (c.setKeypair P id {k with refcount := k.refcount + 1})
          intro _
          exact c.pure P _
      | none =>
        apply c.nativeStore
        intro initial
        exact hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial)
  have hq (pid) := ProductAmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  simp only [sendStagedPacketsPrefix, liftWGObserver_bind]
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getPeerMixed pid))
      (fun p h w => I h w ∧ (identityView w.wg).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro p
  apply PrefixEnsures.bind (branch_spec (fun s => s.1.slots pid = some p.internalId) _ _)
  intro empty
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
  · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := []}).consequence
      (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (keyGet (fun _ => True) p.keypairCurrent))
    intro kp
    have hout := stagedOutNokeyPrefix_preserves_product c t pid p.staged kp
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro missing
    try simp only [apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact hout false
    · cases kp with
      | none => exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
      | some id =>
        dsimp only
        simp only [liftWGObserver_bind]
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
        intro k
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
        intro invalid
        try simp only [liftWGObserver_bind, apply_ite]
        split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
        · exact hout false
        · apply PrefixPreserves.bind (ProductAmbientContracts.drop
            (c.nativeStore (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
          intro expired
          try simp only [apply_ite]
          split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
          · exact hout true
          · simp only [liftWGObserver_bind, lift_loop]
            apply PrefixPreserves.bind
            · apply PrefixPreserves.forIn _ _ _ c.safe
              intro pkt acc
              apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
              intro _
              apply PrefixPreserves.bind (ProductAmbientContracts.drop
                (c.nativeStore (fun _ => True) _ ((ipTunnelEcnEncap_sameWGWorld pkt).factor wgStoreView)))
              intro ds
              apply keypairUpdateThen_preserves_product c id
                (fun k => {k with sendingCounter := k.sendingCounter + 1}) (fun _ => rfl)
              intro k
              apply PrefixPreserves.bind (ProductAmbientContracts.drop (branchCmp_spec (fun _ => True) _ _ _ _))
              intro rejected
              split
              · simp only [liftWGObserver_bind, liftWGObserver_pure]
                apply PrefixPreserves.bind (hout true)
                intro _
                exact PrefixPreserves.pure c.safe _
              · exact PrefixPreserves.pure c.safe _
            · intro acc
              rcases acc with ⟨done, packetsCb⟩
              cases done with
              | some result => exact PrefixPreserves.pure c.safe result
              | none =>
                simp only [liftWGObserver_bind, lift_map]
                apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
                intro _
                apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.peerDeref (fun _ => True) _))
                intro peer
                apply PrefixPreserves.bind (c.peerGet peer)
                intro _
                apply PrefixPreserves.bind (PrefixPreserves.mapM packetsCb _ c.safe (fun p => t.alloc p))
                intro item
                exact createDataPrefix_preserves_product c t pid item


theorem sendKeepalivePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendKeepalivePrefix pid)) := by
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  simp only [sendKeepalivePrefix, liftWGObserver_bind]
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getPeerMixed pid))
      (fun p h w => I h w ∧ (identityView w.wg).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro p
  let P := fun s : IdentityView => s.1.slots pid = some p.internalId
  apply PrefixEnsures.bind (branch_spec P _ _)
  intro empty
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
  · apply PrefixEnsures.bind (c.nativeStore P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) (fun w => wgStoreView w = initial)))
    intro alloc
    apply PrefixEnsures.bind (branch_spec P _ _)
    intro noMem
    try simp only []
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
    · apply PrefixEnsures.bind (c.nativeStore P _ getDev_sameWGStore)
      intro d
      apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := p.staged ++ [{mtu := d.mtu}]}).consequence
        (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
      intro _
      exact sendStagedPacketsPrefix_preserves_product c t pid
  · exact PrefixEnsures.consequence (sendStagedPacketsPrefix_preserves_product c t pid)
      (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)


end Leanux.Proofs.WG.Lifetimes
