import Leanux.Proofs.WG.Queues.RxMaintenanceFrames
import Leanux.Proofs.WG.Lifetimes.TxStaging

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original staged-TX helpers retain surviving receive queues. Their cleanup
may delete a peer on malformed ownership states, so retention rather than
unconditional equality is the compositional contract. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem txDevice_rxQueues (u : TxDeviceUpdate) : SameView rxQueues (modifyDev u.apply) :=
  modifyDev_rxQueues _ (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_rxQueues (pid : PeerId) : SameView rxQueues (cpumaskChooseOnline pid) := by
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
        | (funext i
           simp only [rxQueues, hd, Option.bind_some]
           exact congrFun (rxMap_insert_same d.ifindex d.peers pid p
             {p with serialWorkCpu := some 0} hp rfl rfl) i)

theorem enqueuePerDeviceAndPeer_rxQueues (pid : PeerId) (item : List SkbId) :
    SameView rxQueues (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro initial
  let P := fun view : RxView => view = initial
  have skb {α : Type} (a : SkbM α) :
      Preserves (fun w => P (rxQueues w)) (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
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
    apply hoare_bind _ _ (getPeer_rx_spec P pid)
    intro p
    let Q := fun w => P (rxQueues w) ∧ CurrentRx (rxQueues w) pid p
    apply hoare_bind _ _ (ambient (AmbientM.branch .enqueuePeerQueueFull
      (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) Q)
    intro full
    cases full with
    | true =>
      exact hoare_consequence (hoare_pure (-ENOSPC) Q) (fun _ h => h)
        (fun _ _ h => h.2.1)
    | false =>
      apply hoare_bind _ _ (hoare_consequence
        (setPeer_rx_spec P pid {p with txQueue := p.txQueue.enqueue item})
        (fun _ h => h) (fun _ _ h => h))
      intro _
      apply preserves_bind ((rxQueues_kernel getDev_sameWGStore).wp P)
      intro d
      apply preserves_bind ((rxQueues_kernel (cpumaskNextOnlineFrom_sameStore d.encryptLastCpu)).wp P)
      intro cpu
      apply preserves_bind ((txDevice_rxQueues (.cpu cpu)).wp P)
      intro _
      apply preserves_bind (ambient (AmbientM.branch .enqueueRingFull d.encryptQueue.full) _)
      intro full
      cases full with
      | true => exact preserves_pure (-EPIPE)
      | false =>
        apply preserves_bind (ambient (AmbientM.queueDeviceWork .encryptWorker) _)
        intro _
        apply preserves_bind ((txDevice_rxQueues (.ring item)).wp P)
        intro _
        exact preserves_pure 0


/- Checked decomposition of a fixed receive-retention predicate. -/
open Lean Meta Elab Tactic in
elab "rx_retention_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a retention contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
elab "rx_retention_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``Preserves do throwError "not a retention contract"
  let .app property action := target | throwError "missing action"
  let action := action.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  let head := action.getAppFn.constName?
  if head == some ``Bind.bind then
    evalTactic (← `(tactic| refine preserves_bind ?_ ?_))
  else if head == some ``Pure.pure then
    evalTactic (← `(tactic| exact preserves_pure _))
  else if head == some ``ite || head == some ``dite then
    evalTactic (← `(tactic| split))
  else if head == some ``liftM then
    evalTactic (← `(tactic| unfold liftM))
  else if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
  else
    throwError "unhandled retention action head {head}"

theorem enqueuePerPeerTx_rxQueues (item : List SkbId) (state : PacketState) :
    RetainsRx (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have hp : Preserves P (enqueuePerPeerTx item state) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
    have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
      apply hoare_liftSkb a
      intro w d store hi hd
      unfold P rxQueues at hi ⊢
      simpa only [hd, Option.bind_some] using hi
    have stopped {α : Type} (e : Stop) : Preserves P (throw e : WG.M α) := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient x v ambient' _ hr
      cases hr
    have device : Preserves P getDev := by
      unfold getDev invariant
      repeat' first
        | (rx_retention_head get; exact hoare_consequence (hoare_get P)
            (fun _ h => h) (fun _ _ h => h.2))
        | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
        | (rx_retention_head MonadLift.monadLift; exact ambient _)
        | rx_retention_step
    unfold enqueuePerPeerTx
    simp (config := { zeta := true }) only
      [getTxSkb, setTxSkb, peekQueuedUnit, recordQueued, invariant]
    repeat' first
      | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
      | (rx_retention_head peerGet; exact (peerGet_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head getPeer; exact (getPeer_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head peerPut; exact RetainsRx.wp (peerPut_rxQueues _) s)
      | (rx_retention_head cpumaskChooseOnline; exact (cpumaskChooseOnline_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head getDev; exact device)
      | (rx_retention_head modifyDev; exact (txDevice_rxQueues (.work _)).wp (ResidentsRetained s))
      | (rx_retention_head liftSkb; exact skb _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head throw; exact stopped _)
      | (rx_retention_head MonadExceptOf.throw; exact stopped _)
      | rx_retention_step
  apply hoare_consequence hp
  · intro w he
    dsimp only [P]
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem createData_rxQueues (pid : PeerId) (item : List SkbId) : RetainsRx (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have main : Preserves P (createData pid item) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
    have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
      apply hoare_liftSkb a
      intro w d store hi hd
      unfold P rxQueues at hi ⊢
      simpa only [hd, Option.bind_some] using hi
    have loop {α β : Type} (xs : List α) (initial : β)
        (f : α → β → WG.M (ForInStep β))
        (hf : ∀ a b, Preserves P (f a b)) : Preserves P (forIn xs initial f) :=
      list_view_spec rxQueues (ResidentsRetained s) xs initial f hf
    unfold createData
    simp (config := { zeta := true }) only [branch, invariant, getTxSkb, freeTxSkb]
    repeat' first
      | (rx_retention_head getPeer; exact (getPeer_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head enqueuePerDeviceAndPeer; exact (enqueuePerDeviceAndPeer_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head enqueuePerPeerTx; exact RetainsRx.wp (enqueuePerPeerTx_rxQueues _ _) s)
      | (rx_retention_head keypairPut; exact (keypairPut_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head peerPut; exact RetainsRx.wp (peerPut_rxQueues _) s)
      | (rx_retention_head liftSkb; exact skb _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ForIn.forIn; apply loop)
      | rx_retention_step
  apply hoare_consequence main
  · intro w he
    dsimp only [P]
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem stagedOutNokey_rxQueues (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsRx (stagedOutNokey pid packets keypair invalid) := by
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have restore : Preserves P (do
      setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}) := by
    simp only [getPeer_twice]
    exact (modifyPeer_rxQueues pid (fun p => {p with staged := packets ++ p.staged})
      (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  let tail : WG.M Unit := do
    keypairPut keypair false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}
    sendQueuedHandshakeInitiation pid false
  have ht : Preserves P tail := by
    unfold tail
    apply preserves_bind ((keypairPut_rxQueues keypair false).wp (ResidentsRetained s))
    intro _
    apply preserves_bind
    · apply list_view_spec rxQueues (ResidentsRetained s)
      intro _ _
      exact preserves_bind (ambient (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => preserves_pure _)
    · intro _
      apply preserves_bind (ambient (AmbientM.branch .stagedOrphanWalk false))
      intro _
      simpa only [bind_assoc] using preserves_bind restore
        (fun _ => RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) s)
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
        apply preserves_bind ((getKeypair_rxQueues id).wp (ResidentsRetained s))
        intro key
        apply preserves_bind ((setKeypair_rxQueues id
          {key with sending := {key.sending with isValid := false}}).wp (ResidentsRetained s))
        intro _
        exact ht
  apply hoare_consequence main
  · intro w he
    change ResidentsRetained s (rxQueues w)
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem sendStagedPackets_rxQueues (pid : PeerId) : RetainsRx (sendStagedPackets pid) := by
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  have loop {α β : Type} (xs : List α) (initial : β)
      (f : α → β → WG.M (ForInStep β))
      (hf : ∀ a b, Preserves P (f a b)) : Preserves P (forIn xs initial f) :=
    list_view_spec rxQueues (ResidentsRetained s) xs initial f hf
  have allocate (packets : List DataPacket) : Preserves P (packets.mapM newTxSkb) :=
    mapM_view_spec rxQueues (ResidentsRetained s) newTxSkb packets (fun p => skb (SkbStore.newTx p))
  have noKey (packets : List Packet) (kp : Option KeypairId) (invalid : Bool) :
      Preserves P (stagedOutNokey pid packets kp invalid) :=
    RetainsRx.wp (stagedOutNokey_rxQueues pid packets kp invalid) s
  have main : Preserves P (sendStagedPackets pid) := by
    unfold sendStagedPackets
    apply hoare_bind _ _ (getPeer_rx_spec (ResidentsRetained s) pid)
    intro p
    let Q := fun w => P w ∧ CurrentRx (rxQueues w) pid p
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) Q)
    intro empty
    cases empty with
    | true =>
      exact hoare_consequence (hoare_pure () Q) (fun _ h => h) (fun _ _ h => h.2.1)
    | false =>
      apply hoare_bind _ _ (hoare_consequence
        (setPeer_rx_spec (ResidentsRetained s) pid {p with staged := []})
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
        | (rx_retention_head keypairGet; exact (keypairGet_rxQueues _).wp (ResidentsRetained s))
        | (rx_retention_head getKeypair; exact (getKeypair_rxQueues _).wp (ResidentsRetained s))
        | (rx_retention_head setKeypair; exact (setKeypair_rxQueues _ _).wp (ResidentsRetained s))
        | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp P)
        | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp P)
        | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
        | (rx_retention_head peerGet; exact (peerGet_rxQueues _).wp (ResidentsRetained s))
        | (rx_retention_head createData; exact RetainsRx.wp (createData_rxQueues _ _) s)
        | (rx_retention_head List.mapM; exact allocate _)
        | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
        | (rx_retention_head MonadLift.monadLift; exact ambient _)
        | (rx_retention_head ForIn.forIn; apply loop)
        | rx_retention_step
  apply hoare_consequence main
  · intro w he
    change ResidentsRetained s (rxQueues w)
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.Queues
