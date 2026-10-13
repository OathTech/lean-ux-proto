import Leanux.Proofs.WG.Lifetimes.TxEnqueue

set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-! Complete staged-send and keepalive callers. Staged Packet values are local
payloads; only their later newTxSkb calls allocate resident packet identities.
The no-key restoration deliberately retains both original peer getters. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem ipTunnelEcnEncap_sameKernel (pkt : Packet) : SameKernel (ipTunnelEcnEncap pkt) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol, branch, invariant, unsupported]

def purgeStagedPacketsPrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  liftPrefix (modifyDev fun d => { d with txDropped := d.txDropped + p.staged.length })
  setPeerMixed pid { p with staged := [] }


def stagedOutNokeyPrefix (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId)
    (invalid : Bool) : MixedM Unit := do
  if invalid then
    let some id := keypair | liftPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    setKeypairPrefix id { k with sending := { k.sending with isValid := false } }
  keypairPutPrefix keypair false
  for _ in packets do _ ← liftPrefix (branch .stagedOrphanWalk true)
  _ ← liftPrefix (branch .stagedOrphanWalk false)
  setPeerMixed pid { (← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged }
  sendQueuedHandshakeInitiationPrefix pid false

def stagedOutNokey (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId)
    (invalid : Bool) : M Unit := do
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
  if ← liftPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  let packets := p.staged
  setPeerMixed pid { p with staged := [] }
  let keypair ← keypairGetPrefix p.keypairCurrent
  let outNokey := stagedOutNokeyPrefix pid packets keypair
  if ← liftPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftPrefix (invariant "unreachable")
  let k ← getKeypairPrefix id
  if ← liftPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  if ← liftPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftPrefix (branch .stagedNonceIterate true)
    let ds ← liftPrefix (ipTunnelEcnEncap pkt)
    let k ← getKeypairPrefix id
    let nonce := k.sendingCounter
    setKeypairPrefix id { k with sendingCounter := k.sendingCounter + 1 }
    if ← liftPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then return ← outNokey true
    packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
  _ ← liftPrefix (branch .stagedNonceIterate false)
  peerGetMixed (← getKeypairPrefix id).peer
  let item ← packetsCb.mapM newTxSkbPrefix
  createDataPrefix pid item


def sendKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .keepaliveStagedEmpty p.staged.isEmpty) then
    if ← liftPrefix (branch .keepaliveNoMem !(← liftPrefix (hiddenAlloc .keepaliveSkb))) then return
    setPeerMixed pid { p with staged := p.staged ++ [{ mtu := (← liftPrefix getDev).mtu }] }
  sendStagedPacketsPrefix pid


theorem purgeStagedPacketsPrefix_erases (pid : PeerId) :
    ErasesPrefix (purgeStagedPacketsPrefix pid) (purgeStagedPackets pid) := by
  unfold purgeStagedPacketsPrefix purgeStagedPackets
  exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ => setPeerMixed_erases _ _))

theorem purgeStagedPacketsPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (purgeStagedPacketsPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold purgeStagedPacketsPrefix
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (t.device (fun s => True ∧ s.1.slots pid = some p.internalId) (.dropped p.staged.length))
  intro _
  exact c.setPeer (fun _ => True) pid {p with staged := []}

theorem keypairUpdateThen_preserves (c : AmbientContracts I) (id : KeypairId)
    (f : Keypair → Keypair) (hf : ∀ k, (f k).internalId = k.internalId)
    (next : Keypair → MixedM α) (hn : ∀ k, PrefixPreserves I LifetimeEvent.Safe (next k)) :
    PrefixPreserves I LifetimeEvent.Safe
      (do let k ← getKeypairPrefix id; setKeypairPrefix id (f k); next k) := by
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (getKeypairPrefix id)
      (fun k h w => I h w ∧ (identityView w).2.1 id = some k.internalId) :=
    (c.getKeypair (fun _ => True) id).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro k
  apply PrefixEnsures.bind ((c.setKeypair (fun _ => True) id (f k)).consequence
    (fun _ _ hi => ⟨hi.1, True.intro, (hf k) ▸ hi.2⟩) (fun _ _ _ hi => hi.1))
  intro _
  exact hn k

theorem stagedRestore_preserves (c : AmbientContracts I) (pid : PeerId) (packets : List Packet) :
    PrefixPreserves I LifetimeEvent.Safe
      (do setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged}) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := packets ++ q.staged}

theorem stagedOutNokeyPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (packets : List Packet) (kp : Option KeypairId) (invalid : Bool) :
    PrefixPreserves I LifetimeEvent.Safe (stagedOutNokeyPrefix pid packets kp invalid) := by
  have hq (pid) := AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  unfold stagedOutNokeyPrefix
  have tail : PrefixPreserves I LifetimeEvent.Safe
      (do
        keypairPutPrefix kp false
        for _ in packets do _ ← liftPrefix (branch .stagedOrphanWalk true)
        _ ← liftPrefix (branch .stagedOrphanWalk false)
        setPeerMixed pid {(← getPeerMixed pid) with staged := packets ++ (← getPeerMixed pid).staged}
        sendQueuedHandshakeInitiationPrefix pid false) := by
    apply PrefixPreserves.bind (t.put _ _)
    intro _
    apply PrefixPreserves.bind (PrefixPreserves.forIn _ _ _ c.safe (fun _ _ =>
      PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        (fun _ => PrefixPreserves.pure c.safe _)))
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    have hr := stagedRestore_preserves c pid packets
    simpa only [bind_assoc] using PrefixPreserves.bind hr (fun _ =>
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
    ErasesPrefix (stagedOutNokeyPrefix pid packets kp invalid) (stagedOutNokey pid packets kp invalid) := by
  unfold stagedOutNokeyPrefix stagedOutNokey
  cases invalid <;> cases kp <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact getKeypairPrefix_erases _
    | with_reducible exact setKeypairPrefix_erases _ _
    | with_reducible exact keypairPutPrefix_erases _ _
    | with_reducible exact sendQueuedHandshakeInitiationPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem sendStagedPacketsPrefix_erases (pid : PeerId) :
    ErasesPrefix (sendStagedPacketsPrefix pid) (sendStagedPackets pid) := by
  unfold sendStagedPacketsPrefix sendStagedPackets
  apply erasesPrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro empty
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (setPeerMixed_erases _ _)
    intro _
    apply erasesPrefix_bind (keypairGetPrefix_erases _)
    intro kp
    have hout (invalid : Bool) := stagedOutNokeyPrefix_erases pid p.staged kp invalid
    change ErasesPrefix
      (do
        if ← liftPrefix (branch .stagedNoKeypair kp.isNone) then return ← stagedOutNokeyPrefix pid p.staged kp false
        _) _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact erasesPrefix_lift _
      | some id =>
        apply erasesPrefix_bind (getKeypairPrefix_erases _)
        intro k
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro invalid
        split
        · exact hout false
        · apply erasesPrefix_bind (erasesPrefix_lift _)
          intro expired
          split
          · exact hout true
          · repeat' first
              | with_reducible exact getKeypairPrefix_erases _
              | with_reducible exact setKeypairPrefix_erases _ _
              | with_reducible exact peerGetMixed_erases _
              | with_reducible exact createDataPrefix_erases _ _
              | with_reducible exact PacketAllocation.erases (.tx _)
              | with_reducible exact erasesPrefix_lift _
              | with_reducible exact erasesPrefix_pure _
              | exact hout true
              | with_reducible apply erasesPrefix_mapM
              | with_reducible apply erasesPrefix_forIn
              | with_reducible apply erasesPrefix_ite
              | with_reducible apply erasesPrefix_bind
              | split
              | (solve | simp_all only)
              | (with_reducible intro x; try dsimp only)
            all_goals first
              | exact PacketAllocation.erases (.tx _)
              | (solve | simp_all)
              | (simp_all only [Option.some.injEq]; exact hout true)

theorem sendStagedPacketsPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (sendStagedPacketsPrefix pid) := by
  have hq (pid) := AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  unfold sendStagedPacketsPrefix
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro p
  apply PrefixEnsures.bind (c.branch (fun s => s.1.slots pid = some p.internalId) _ _)
  intro empty
  split
  · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := []}).consequence
      (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (keypairGetPrefix_spec_ambient c (fun _ => True) p.keypairCurrent))
    intro kp
    have hout := stagedOutNokeyPrefix_preserves_ambient c t pid p.staged kp
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some id =>
        apply PrefixPreserves.bind (AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
        intro k
        apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro invalid
        split
        · exact hout false
        · apply PrefixPreserves.bind (AmbientContracts.drop
            (c.kernel (fun _ => True) _ (branchExpired_sameKernel _ _ _)))
          intro expired
          split
          · exact hout true
          · repeat' first
              | with_reducible exact AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _)
              | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
              | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
              | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (ipTunnelEcnEncap_sameKernel _))
              | with_reducible exact c.peerGet _
              | with_reducible exact t.alloc _
              | with_reducible exact createDataPrefix_preserves_ambient c t _ _
              | with_reducible exact PrefixPreserves.pure c.safe _
              | exact hout true
              | apply keypairUpdateThen_preserves c id (fun k => {k with sendingCounter := k.sendingCounter + 1}) (fun _ => rfl)
              | with_reducible apply PrefixPreserves.mapM _ _ c.safe
              | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
              | with_reducible apply PrefixPreserves.bind
              | split
              | (with_reducible intro x; try dsimp only)

theorem sendKeepalivePrefix_erases (pid : PeerId) :
    ErasesPrefix (sendKeepalivePrefix pid) (sendKeepalive pid) := by
  unfold sendKeepalivePrefix sendKeepalive
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem sendKeepalivePrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (sendKeepalivePrefix pid) := by
  unfold sendKeepalivePrefix
  apply PrefixEnsures.preserves
  have hg : PrefixEnsures I LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hg
  intro p
  let P := fun s : IdentityView => s.1.slots pid = some p.internalId
  apply PrefixEnsures.bind (c.branch P _ _)
  intro empty
  split
  · apply PrefixEnsures.bind (c.kernel P _ (hiddenAlloc_sameKernel _))
    intro alloc
    apply PrefixEnsures.bind (c.branch P _ _)
    intro noMem
    split
    · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
    · apply PrefixEnsures.bind (c.kernel P _ getDev_sameKernel)
      intro d
      apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with staged := p.staged ++ [{mtu := d.mtu}]}).consequence
        (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
      intro _
      exact sendStagedPacketsPrefix_preserves_ambient c t pid
  · exact PrefixEnsures.consequence (sendStagedPacketsPrefix_preserves_ambient c t pid)
      (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.Lifetimes
