import Leanux.Proofs.WG.AllowedIps.RoutingRetains
import Leanux.Proofs.WG.Queues.RxTxFrames

/-! Concrete routing frames for the original staged-send helpers. Packet,
key and queue effects remain unrestricted; peer release may delete a resident.
The existing source factors and matcher environment are shared with RX frames. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem RetainsRoutingCall.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : ProjectedRetainsRoutingCall project a) (s : Option RoutingState) :
    ⦃fun w => ⌜RetainsRouting s (routingView (project w))⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsRouting s (routingView (project w))⌝⦄ :=
  ProjectedAction.wp h (RetainsRouting s) (fun _ _ hr hs => hs.trans hr)

theorem requireNotPending_routing (pid : PeerId) (why : String) :
    SameView routingView (requireNotPending pid why) :=
  SameView.pure _ _

theorem getPeer_routing (pid : PeerId) : SameView routingView (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  have hv := (Peers.getPeer_current pid w v p ambient ambient' hr).1
  cases hv
  rfl

theorem getKeypair_routing (id : KeypairId) : SameView routingView (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      have he := CounterWindow.getKeypair_run w ambient d id old hd hk
      rw [he] at hr
      cases hr
      rfl

theorem ownerDeref_routing (owner : IndexOwner) : SameView routingView owner.peerDeref := by
  intro s
  exact indexOwner_peerDeref_preserves owner (fun w => routingView w = s)

theorem ownerWord_routing (owner : IndexOwner) : SameView routingView owner.peerWord := by
  intro s
  exact indexOwner_peerWord_preserves owner (fun w => routingView w = s)

theorem setKeypair_routing (id : KeypairId) (k : Keypair) : SameView routingView (setKeypair id k) :=
  modifyDev_routing _ (fun _ => rfl)

theorem peerGet_routing (pid : PeerId) : SameView routingView (peerGet pid) := by
  intro s
  let P := fun view : Option RoutingState => view = s
  have inc (old : Nat) (Q : WGWorld → Prop) : Preserves Q (refcountInc old : WG.M Unit) := by
    unfold refcountInc
    simp only [branch, branchCmp, unsupported]
    repeat' first
      | (rx_retention_head MonadLiftT.monadLift; exact hoare_liftAmbient _ Q)
      | (rx_retention_head MonadLift.monadLift; exact hoare_liftAmbient _ Q)
      | rx_retention_step
  unfold peerGet requireNotPending
  simp only [pure_bind]
  apply hoare_bind _ _ (routing_getPeer P pid)
  intro p
  apply hoare_bind _ _ (inc p.refcount (fun w => P (routingView w) ∧
    (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList))
  intro _
  exact routing_setPeer P pid {p with refcount := p.refcount + 1}

theorem keypairGet_routing (kp : Option KeypairId) : SameView routingView (keypairGet kp) := by
  intro s
  let P := fun w : WGWorld => routingView w = s
  change Preserves P (keypairGet kp)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  unfold keypairGet refcountIncNotZero
  simp (config := { zeta := true }) only [branch, branchCmp, invariant, unsupported]
  repeat' first
    | (rx_retention_head getKeypair; exact (getKeypair_routing _).wp (fun view => view = s))
    | (rx_retention_head setKeypair; exact (setKeypair_routing _ _).wp (fun view => view = s))
    | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
    | (rx_retention_head MonadLift.monadLift; exact ambient _)
    | rx_retention_step

theorem keypairPut_routing (kp : Option KeypairId) (now : Bool) :
    SameView routingView (keypairPut kp now) := by
  intro s
  let P := fun w : WGWorld => routingView w = s
  change Preserves P (keypairPut kp now)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have remove (id : KeypairId) : Preserves P (monadLift (indexRemove (.keypair id)) : WG.M Unit) := by
    apply hoare_liftIndex (indexRemove (.keypair id)) P
    intro w d table hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have removal (id : KeypairId) : Preserves P (do
      _ ← IndexOwner.peerDeref (.keypair id)
      monadLift (indexRemove (.keypair id)) : WG.M Unit) :=
    preserves_bind (indexOwner_peerDeref_preserves (.keypair id) P) (fun _ => remove id)
  have erase (id : KeypairId) : Preserves P (modifyDev fun d => {d with keypairs := d.keypairs.erase id}) :=
    (modifyDev_routing (fun d => {d with keypairs := d.keypairs.erase id})
      (fun _ => rfl)).wp (fun view => view = s)
  have dec (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    unfold refcountDecAndTest
    simp only [branch, branchCmp, unsupported]
    repeat' first
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | rx_retention_step
  let tail (id : KeypairId) (k : Keypair) : WG.M Unit := do
    setKeypair id {k with refcount := k.refcount - 1}
    if ← branch .keypairKrefPutReleased (← refcountDecAndTest k.refcount) then
      _ ← IndexOwner.peerDeref (.keypair id)
      indexRemove (.keypair id)
      modifyDev fun d => {d with keypairs := d.keypairs.erase id}
  have ht (id : KeypairId) (k : Keypair) : Preserves P (tail id k) := by
    unfold tail
    apply preserves_bind ((setKeypair_routing id {k with refcount := k.refcount - 1}).wp
      (fun view => view = s))
    intro _
    apply preserves_bind (dec k.refcount)
    intro released
    apply preserves_bind (ambient (AmbientM.branch .keypairKrefPutReleased released))
    intro result
    split
    · simpa only [bind_assoc] using preserves_bind (removal id) (fun _ => erase id)
    · exact preserves_pure _
  unfold keypairPut
  apply preserves_bind (ambient (AmbientM.branch .keypairPutNull kp.isNone))
  intro isNull
  split
  · exact preserves_pure _
  · cases kp with
    | none => exact ambient (AmbientM.invariant "unreachable")
    | some id =>
      apply preserves_bind ((getKeypair_routing id).wp (fun view => view = s))
      intro k
      apply preserves_bind (ambient (AmbientM.branch .keypairPutUnreferenceNow now))
      intro unreference
      split
      · simpa only [bind_assoc, tail] using preserves_bind (removal id) (fun _ => ht id k)
      · simpa only [bind_assoc, tail] using ht id k

theorem sendQueuedHandshakeInitiation_routing (pid : PeerId) (retry : Bool) :
    RetainsRoutingCall (sendQueuedHandshakeInitiation pid retry) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have reset : Preserves P (do
      setPeer pid {(← getPeer pid) with timerHandshakeAttempts := 0}) :=
    hoare_bind _ _ (routing_getPeer (RetainsRouting s) pid)
      (fun p => routing_setPeer (RetainsRouting s) pid {p with timerHandshakeAttempts := 0})
  have pending : Preserves P (do
      setPeer pid {(← getPeer pid) with handshakePending := true}) :=
    hoare_bind _ _ (routing_getPeer (RetainsRouting s) pid)
      (fun p => routing_setPeer (RetainsRouting s) pid {p with handshakePending := true})
  have hqueue := (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl)).wp (RetainsRouting s)
  have scheduled : Preserves P (do
      setPeer pid { (← getPeer pid) with handshakePending := true }
      recordQueued .sendWorker pid
      modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) := by
    simpa only [bind_assoc, recordQueued, P] using preserves_bind pending (fun _ =>
      preserves_bind (ambient (AmbientM.recordQueued .sendWorker pid)) (fun _ => hqueue))
  let tail : WG.M Unit := do
    let p ← getPeer pid
    if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
    if ← branch .queuedDead p.isDead then return
    peerGet pid
    if ← branch .queuedAlreadyQueued (p.handshakePending && !(← peekQueuedUnit .sendWorker pid)) then
      peerPut (some pid)
      return
    setPeer pid { (← getPeer pid) with handshakePending := true }
    recordQueued .sendWorker pid
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
  have ht : Preserves P tail := by
    unfold tail
    apply preserves_bind ((getPeer_routing pid).wp (RetainsRouting s))
    intro p
    apply preserves_bind ((branchExpired_sameWGWorld .queuedNotExpired p.lastSentHandshake
      REKEY_TIMEOUT (!·)).wp P)
    intro expired
    split
    · exact preserves_pure _
    · apply preserves_bind (ambient (AmbientM.branch .queuedDead p.isDead))
      intro dead
      split
      · exact preserves_pure _
      · apply preserves_bind ((peerGet_routing pid).wp (RetainsRouting s))
        intro _
        apply preserves_bind (ambient (AmbientM.peekQueuedUnit .sendWorker pid))
        intro queued
        apply preserves_bind (ambient (AmbientM.branch .queuedAlreadyQueued (p.handshakePending && !queued)))
        intro already
        split
        · exact preserves_bind (RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s)
            (fun _ => preserves_pure _)
        · exact scheduled
  have main : Preserves P (sendQueuedHandshakeInitiation pid retry) := by
    unfold sendQueuedHandshakeInitiation
    apply preserves_bind (ambient (AmbientM.branch .queuedNotRetry !retry))
    intro notRetry
    split
    · simpa only [bind_assoc] using preserves_bind reset (fun _ => ht)
    · exact ht
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem txDevice_routing (u : TxDeviceUpdate) : SameView routingView (modifyDev u.apply) :=
  modifyDev_routing _ (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_routing (pid : PeerId) : SameView routingView (cpumaskChooseOnline pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hd : w.dev with
  | none =>
    simp [cpumaskChooseOnline, getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      simp [cpumaskChooseOnline, getPeer, getDev, setPeer, modifyDev, hd, hp,
        branch, AmbientM.branch, Nat.mod_one] at hr
      repeat' split at hr
      all_goals simp_all
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals first
        | rfl
        | (simpa only [routingView, hd, Option.map_some] using congrArg some
            (routingState_insert_same d pid p {p with serialWorkCpu := some 0} hp rfl))

theorem enqueuePerDeviceAndPeer_routing (pid : PeerId) (item : List SkbId) :
    SameView routingView (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro initial
  let P := fun view : Option RoutingState => view = initial
  have skb {α : Type} (a : SkbM α) :
      Preserves (fun w => P (routingView w)) (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Preserves Q (monadLift a : WG.M α) := hoare_liftAmbient a Q
  unfold enqueuePerDeviceAndPeer
  cases item.head? with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  | some first =>
    apply hoare_bind _ _ (skb (SkbStore.setTx first fun p => {p with state := .uncrypted}))
    intro _
    apply hoare_bind _ _ (routing_getPeer P pid)
    intro p
    let Q := fun w => P (routingView w) ∧ (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
    apply hoare_bind _ _ (ambient (AmbientM.branch .enqueuePeerQueueFull
      (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) Q)
    intro full
    cases full with
    | true =>
      exact hoare_consequence (hoare_pure (-ENOSPC) Q) (fun _ h => h)
        (fun _ _ h => h.2.1)
    | false =>
      apply hoare_bind _ _ (hoare_consequence
        (routing_setPeer P pid {p with txQueue := p.txQueue.enqueue item})
        (fun _ h => h) (fun _ _ h => h))
      intro _
      apply preserves_bind ((routing_kernel _ getDev_sameWGStore).wp P)
      intro d
      apply preserves_bind ((routing_kernel _ (cpumaskNextOnlineFrom_sameStore d.encryptLastCpu)).wp P)
      intro cpu
      apply preserves_bind ((txDevice_routing (.cpu cpu)).wp P)
      intro _
      apply preserves_bind (ambient (AmbientM.branch .enqueueRingFull d.encryptQueue.full) _)
      intro full
      cases full with
      | true => exact preserves_pure (-EPIPE)
      | false =>
        apply preserves_bind (ambient (AmbientM.queueDeviceWork .encryptWorker) _)
        intro _
        apply preserves_bind ((txDevice_routing (.ring item)).wp P)
        intro _
        exact preserves_pure 0



theorem enqueuePerPeerTx_routing (item : List SkbId) (state : PacketState) :
    RetainsRoutingCall (enqueuePerPeerTx item state) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have main : Preserves P (enqueuePerPeerTx item state) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
    have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
      apply hoare_liftSkb a
      intro w d store hi hd
      unfold P routingView at hi ⊢
      simpa only [hd, Option.map_some, routingState] using hi
    have device := (routing_kernel _ getDev_sameWGStore).wp (RetainsRouting s)
    unfold enqueuePerPeerTx
    simp (config := { zeta := true }) only
      [getTxSkb, setTxSkb, peekQueuedUnit, recordQueued, invariant]
    repeat' first
      | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
      | (rx_retention_head peerGet; exact (peerGet_routing _).wp (RetainsRouting s))
      | (rx_retention_head getPeer; exact (getPeer_routing _).wp (RetainsRouting s))
      | (rx_retention_head peerPut; exact RetainsRoutingCall.wp (peerPut_retainsRouting _) s)
      | (rx_retention_head cpumaskChooseOnline; exact (cpumaskChooseOnline_routing _).wp (RetainsRouting s))
      | (rx_retention_head getDev; exact device)
      | (rx_retention_head modifyDev; exact (txDevice_routing (.work _)).wp (RetainsRouting s))
      | (rx_retention_head liftSkb; exact skb _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head MonadExceptOf.throw; exact hoare_throw _)
      | rx_retention_step
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem createData_routing (pid : PeerId) (item : List SkbId) : RetainsRoutingCall (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have main : Preserves P (createData pid item) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
    have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
      apply hoare_liftSkb a
      intro w d store hi hd
      unfold P routingView at hi ⊢
      simpa only [hd, Option.map_some, routingState] using hi
    have loop {α β : Type} (xs : List α) (initial : β)
        (f : α → β → WG.M (ForInStep β))
        (hf : ∀ a b, Preserves P (f a b)) : Preserves P (forIn xs initial f) :=
      list_view_spec routingView (RetainsRouting s) xs initial f hf
    unfold createData
    simp (config := { zeta := true }) only [branch, invariant, getTxSkb, freeTxSkb]
    repeat' first
      | (rx_retention_head getPeer; exact (getPeer_routing _).wp (RetainsRouting s))
      | (rx_retention_head enqueuePerDeviceAndPeer; exact (enqueuePerDeviceAndPeer_routing _ _).wp (RetainsRouting s))
      | (rx_retention_head enqueuePerPeerTx; exact RetainsRoutingCall.wp (enqueuePerPeerTx_routing _ _) s)
      | (rx_retention_head keypairPut; exact (keypairPut_routing _ _).wp (RetainsRouting s))
      | (rx_retention_head peerPut; exact RetainsRoutingCall.wp (peerPut_retainsRouting _) s)
      | (rx_retention_head liftSkb; exact skb _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ForIn.forIn; apply loop)
      | rx_retention_step
  apply hoare_consequence main
  · intro w he
    dsimp only [P]
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem stagedOutNokey_routing (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsRoutingCall (stagedOutNokey pid packets keypair invalid) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have restore : Preserves P (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
    simp only [getPeer_twice]
    exact hoare_bind _ _ (routing_getPeer (RetainsRouting s) pid)
      (fun p => routing_setPeer (RetainsRouting s) pid {p with staged := packets ++ p.staged})
  let tail : WG.M Unit := do
    keypairPut keypair false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}
    sendQueuedHandshakeInitiation pid false
  have ht : Preserves P tail := by
    unfold tail
    apply preserves_bind ((keypairPut_routing keypair false).wp (RetainsRouting s))
    intro _
    apply preserves_bind
    · apply list_view_spec routingView (RetainsRouting s)
      intro _ _
      exact preserves_bind (ambient (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => preserves_pure _)
    · intro _
      apply preserves_bind (ambient (AmbientM.branch .stagedOrphanWalk false))
      intro _
      simpa only [bind_assoc] using preserves_bind restore
        (fun _ => RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s)
  have main : Preserves P (stagedOutNokey pid packets keypair invalid) := by
    unfold stagedOutNokey
    cases invalid with
    | false => exact ht
    | true =>
      cases keypair with
      | none =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient x v ambient' _ hr
        cases hr
      | some id =>
        apply preserves_bind ((getKeypair_routing id).wp (RetainsRouting s))
        intro key
        apply preserves_bind ((setKeypair_routing id
          {key with sending := {key.sending with isValid := false}}).wp (RetainsRouting s))
        intro _
        exact ht
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem sendStagedPackets_routing (pid : PeerId) : RetainsRoutingCall (sendStagedPackets pid) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have loop {α β : Type} (xs : List α) (initial : β)
      (f : α → β → WG.M (ForInStep β))
      (hf : ∀ a b, Preserves P (f a b)) : Preserves P (forIn xs initial f) :=
    list_view_spec routingView (RetainsRouting s) xs initial f hf
  have allocate (packets : List DataPacket) : Preserves P (packets.mapM newTxSkb) :=
    mapM_view_spec routingView (RetainsRouting s) newTxSkb packets (fun p => skb (SkbStore.newTx p))
  have noKey (packets : List Packet) (kp : Option KeypairId) (invalid : Bool) :
      Preserves P (stagedOutNokey pid packets kp invalid) :=
    RetainsRoutingCall.wp (stagedOutNokey_routing pid packets kp invalid) s
  have main : Preserves P (sendStagedPackets pid) := by
    unfold sendStagedPackets
    apply hoare_bind _ _ (routing_getPeer (RetainsRouting s) pid)
    intro p
    let Q := fun w => P w ∧ (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) Q)
    intro empty
    cases empty with
    | true =>
      exact hoare_consequence (hoare_pure () Q) (fun _ h => h) (fun _ _ h => h.2.1)
    | false =>
      apply hoare_bind _ _ (hoare_consequence
        (routing_setPeer (RetainsRouting s) pid {p with staged := []})
        (fun _ h => h) (fun _ _ h => h))
      intro _
      change Preserves P (do
        let keypair ← keypairGet p.keypairCurrent
        let outNokey := stagedOutNokey pid p.staged keypair
        if ← branch .stagedNoKeypair keypair.isNone then return ← outNokey false
        let some id := keypair | invariant "unreachable"
        let k ← getKeypair id
        if ← branch .stagedKeyInvalid !k.sending.isValid then return ← outNokey false
        if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
          return ← outNokey true
        let mut packetsCb : List DataPacket := []
        for pkt in p.staged do
          _ ← branch .stagedNonceIterate true
          let ds ← ipTunnelEcnEncap pkt
          let k ← getKeypair id
          let nonce := k.sendingCounter   -- atomic64_inc_return(&sending_counter) - 1
          setKeypair id { k with sendingCounter := k.sendingCounter + 1 }
          if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then return ← outNokey true
          packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
        _ ← branch .stagedNonceIterate false
        peerGet (← IndexOwner.peerDeref (.keypair id))
        let item ← packetsCb.mapM newTxSkb
        createData pid item)
      simp (config := { zeta := true }) only [branch, branchCmp, invariant]
      repeat' first
        | (rx_retention_head stagedOutNokey; exact noKey _ _ _)
        | (rx_retention_head keypairGet; exact (keypairGet_routing _).wp (RetainsRouting s))
        | (rx_retention_head getKeypair; exact (getKeypair_routing _).wp (RetainsRouting s))
        | (rx_retention_head setKeypair; exact (setKeypair_routing _ _).wp (RetainsRouting s))
        | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp P)
        | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp P)
        | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
        | (rx_retention_head peerGet; exact (peerGet_routing _).wp (RetainsRouting s))
        | (rx_retention_head createData; exact RetainsRoutingCall.wp (createData_routing _ _) s)
        | (rx_retention_head List.mapM; exact allocate _)
        | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
        | (rx_retention_head MonadLift.monadLift; exact ambient _)
        | (rx_retention_head ForIn.forIn; apply loop)
        | rx_retention_step
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem sendKeepalive_routing (pid : PeerId) : RetainsRoutingCall (sendKeepalive pid) := by
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have send := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have main : Preserves P (sendKeepalive pid) := by
    unfold sendKeepalive
    apply hoare_bind _ _ (routing_getPeer (RetainsRouting s) pid)
    intro p
    let Q := fun w => P w ∧
      (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) Q)
    intro empty
    cases empty with
    | false => exact hoare_consequence send (fun _ h => h.1) (fun _ _ h => h)
    | true =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) Q)
      intro allocated
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveNoMem !allocated) Q)
      intro noMem
      cases noMem with
      | true => exact hoare_consequence (hoare_pure () Q) (fun _ h => h) (fun _ _ h => h.2.1)
      | false =>
        have readDev := getDev_sameWGStore.wp (fun store =>
          RetainsRouting s (store.dev.map routingState) ∧
          (store.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList)
        apply hoare_bind _ _ readDev
        intro d
        apply hoare_bind _ _ (routing_setPeer (RetainsRouting s) pid
          {p with staged := p.staged ++ [{mtu := d.mtu}]})
        intro _
        exact send
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
