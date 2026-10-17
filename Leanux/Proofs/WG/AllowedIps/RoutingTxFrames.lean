import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.WG.Queues.TxRingWorker
import Leanux.Proofs.Framing.WGData

/-! Original TX and stack calls preserve routing tables, allocation frontiers
and every surviving resident list. Peer releases may delete residents. These
are normal-endpoint frames, not packet authorization or termination claims. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

abbrev ProductRetainsRoutingCall (a : Leanux.M α) : Prop :=
  ProjectedRetainsRoutingCall World.wg a

theorem RetainsRoutingCall.liftWG {a : WG.M α} (h : RetainsRoutingCall a) :
    ProductRetainsRoutingCall (Leanux.liftWG a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (ProjectedAction.iff_run_ambient _ _ _).mp h _ _ _ _ _ he

private theorem borrowed_routing
    (hb : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    routingView v = routingView w := by
  cases result with
  | none =>
    have hd := congrArg WGStoreView.dev hb
    simpa only [wgStoreView, routingView] using congrArg (Option.map routingState) hd
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    have hv := congrArg WGStoreView.dev hk
    simp only [wgStoreView] at hd hv
    simp [routingView, hv, hd, hs]

theorem lookup_routing (root : Option NodeId) (bits key : Nat) :
    SameView routingView (lookup root bits key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookup_spec root bits key (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupSrc_routing (protocol : Nat) (bytes : List UInt8) :
    SameView routingView (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupDst_routing (family addr : Nat) : SameView routingView (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient result v ambient' rfl hr)

/- Checked source composition for the existing fixed routing predicate. -/
open Lean Meta Elab Tactic in
elab "routing_tx_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``Preserves do throwError "expected a routing preservation contract"
  let .app property action := target | throwError "missing routing action"
  let action := action.consumeMData
  if let .letE name ty value body _ := action then
    if name.toString.startsWith "__do_jp" || name.eraseMacroScopes == `err then
      let claim ← forallTelescope ty fun args _ =>
        mkForallFVars args (mkApp property (mkAppN value args))
      let proof ← mkFreshExprSyntheticOpaqueMVar claim
      let (continuation, next) ← withLocalDeclD name ty fun f => do
        let claim ← forallTelescope ty fun args _ =>
          mkForallFVars args (mkApp property (mkAppN f args))
        withLocalDeclD `routing_join claim fun hf => do
          let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
          return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
      goal.assign (mkApp2 continuation value proof)
      replaceMainGoal [proof.mvarId!, next]
    else
      replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  if let .letE _ _ value body _ := action.getAppFn.consumeMData then
    replaceMainGoal [← goal.replaceTargetDefEq
      (mkApp property (mkAppN (body.instantiate1 value) action.getAppArgs))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  if action.getAppFn.isFVar then
    for decl in ← getLCtx do
      if decl.userName == `routing_join then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
    throwError "missing routing continuation contract"
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
    throwError "unhandled routing action head {head}"

macro "routing_tx_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no routing source fact")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let mut atom ← `(tactic| fail "not a source wrapper")
  for name in #[``Leanux.branch, ``Leanux.branchCmp, ``Leanux.invariant,
      ``Leanux.unsupported, ``Leanux.hiddenAlloc, ``Leanux.skipCut,
      ``Leanux.skipCutSites, ``Leanux.envOk, ``Leanux.WG.andM, ``Leanux.WG.orM,
      ``Leanux.WG.getTxSkb, ``Leanux.WG.setTxSkb, ``Leanux.WG.freeTxSkb,
      ``Leanux.getRouting, ``liftM].reverse do
    let n := Lean.mkCIdent name
    atom ← `(tactic| first | (rx_retention_head $n; unfold $n) | ($atom:tactic))
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic|
    (have routingLoop {S α β : Type} {m : Type → Type} {ps : PostShape}
         [Monad m] [WPMonad m ps] (P : S → Prop) (xs : List α) (b : β)
         (f : α → β → StateT S m (ForInStep β))
         (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
       list_view_spec id P xs b f hf
     have routingDiscard {S α : Type} {m : Type → Type} {ps : PostShape}
         [Monad m] [WPMonad m ps] (P : S → Prop) (a : StateT S m α)
         (ha : Preserves P a) : Preserves P (discard a) :=
       discard_view_spec id P a ha
     $expand
     repeat' first
       | ($use:tactic)
       | ($atom:tactic)
       | (rx_retention_head ForIn.forIn; first | apply routingLoop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
       | (rx_retention_head Functor.discard; apply routingDiscard)
       | routing_tx_step))

theorem sendSkbToPeer_routing (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView routingView (sendSkbToPeer pid bytes ds) := by
  intro s
  let Q := fun t => t = s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have four (e : Endpoint) : Preserves P (send4 e (some pid) bytes ds true) :=
    (send4_routing e (some pid) bytes ds true).wp Q
  have six (e : Endpoint) : Preserves P (send6 e (some pid) bytes ds true) :=
    (send6_routing e (some pid) bytes ds true).wp Q
  have update : Preserves P (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + bytes.length}) :=
    (modifyPeer_routing pid (fun p => {p with txBytes := p.txBytes + bytes.length})
      (fun _ => rfl)).wp Q
  let finish (ret : Int) : WG.M Bool := do
    let sent := ret == 0
    if ← branch .sendSkbOk sent then
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + bytes.length}
    return sent
  have done (ret : Int) : Preserves P (finish ret) := by
    unfold finish
    apply preserves_bind (ambient (AmbientM.branch .sendSkbOk (ret == 0)))
    intro sent
    cases sent with
    | false => exact preserves_pure _
    | true =>
      simpa only [↓reduceIte, bind_assoc] using
        preserves_bind update (fun _ => (preserves_pure (ret == 0) : Preserves P (pure (ret == 0) : WG.M Bool)))
  have source : sendSkbToPeer pid bytes ds = (do
      let p ← getPeer pid
      let family := (p.endpoint.map (·.family)).getD 0
      let e := p.endpoint.getD {family := 0, addr := 0, port := 0}
      let ret ← do
        if ← branch .sendSkbInet (family == AF_INET) then send4 e (some pid) bytes ds true
        else if ← branch .sendSkbInet6 (family == AF_INET6) then send6 e (some pid) bytes ds true
        else pure (-EAFNOSUPPORT)
      finish ret) := by
    simp only [sendSkbToPeer, finish, pure_bind]
  rw [source]
  change Preserves P _
  routing_tx_source [] using [peer, four, six, done, ambient]

theorem timersDataSent_routing (pid : PeerId) : SameView routingView (timersDataSent pid) := by
  intro s
  let Q : Option RoutingState → Prop := fun t => t = s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi

  have jitter : Preserves P (jitterBelowRekeyTimeout .newHandshakeJitter) :=
    (jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).wp P
  have clock : Preserves P (callerJiffies .timerJiffiesDataSent) :=
    (callerJiffies_sameWGWorld .timerJiffiesDataSent).wp P
  have guard : Preserves P (modPeerTimerGuard pid) := (modPeerTimerGuard_routing pid).wp Q
  have arm (n : Nat) (jc : Option UInt64) : Preserves P (armTimer pid .newHandshake n jc) :=
    (armTimer_routing pid .newHandshake n jc).wp Q
  change Preserves P (timersDataSent pid)
  routing_tx_source [timersDataSent] using [peer, jitter, clock, guard, arm, ambient]

theorem keepKeyFresh_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFresh pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi

  have expired (d : Decision) (birth : Int64) (age : Nat) : Preserves P (branchExpired d birth age) :=
    (branchExpired_sameWGWorld d birth age).wp P
  have queued : Preserves P (sendQueuedHandshakeInitiation pid false) :=
    RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  have main : Preserves P (keepKeyFresh pid) := by
    routing_tx_source [keepKeyFresh] using [peer, key, expired, queued, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem createDataDone_routing (pid : PeerId) (item : List SkbId) :
    RetainsRoutingCall (createDataDone pid item) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi

  have traversal : Preserves P (timersTraversal pid) := (timersTraversal_routing pid).wp Q
  have authenticated : Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    (timersAnyAuthenticatedPacketSent_routing pid).wp Q
  have send (bytes : List UInt8) (ds : Nat) : Preserves P (sendSkbToPeer pid bytes ds) :=
    (sendSkbToPeer_routing pid bytes ds).wp Q
  have dataSent : Preserves P (timersDataSent pid) := (timersDataSent_routing pid).wp Q
  have fresh : Preserves P (keepKeyFresh pid) := RetainsRoutingCall.wp (keepKeyFresh_routing pid) s
  have main : Preserves P (createDataDone pid item) := by
    routing_tx_source [createDataDone] using [traversal, authenticated, send, dataSent, fresh, skb, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem txStep_routing (pid : PeerId) : RetainsRoutingCall (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have complete (item : List SkbId) : Preserves P (createDataDone pid item) :=
    RetainsRoutingCall.wp (createDataDone_routing pid item) s
  have key (kp : Option KeypairId) : Preserves P (keypairPut kp false) :=
    (keypairPut_routing kp false).wp Q
  have put : Preserves P (peerPut (some pid)) :=
    RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have dispose (item : List SkbId) (kp : KeypairId) :
      Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have drop : Preserves P (do
      let p ← getPeer pid
      setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    (modifyPeer_routing pid (fun p => {p with txQueue := p.txQueue.dropPeeked})
      (fun _ => rfl)).wp Q
  have body (first : Option (List SkbId)) :
      Preserves P (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [skb, ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none =>
            simp only [hh]
            exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (skb (SkbStore.getTx headId))
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete, dispose, ambient]
  have main : Preserves P (TxDisposition.stepSource pid) := by
    unfold TxDisposition.stepSource
    apply preserves_bind ((getPeer_routing pid).wp Q)
    intro p
    apply preserves_bind ((routing_kernel _ (prevQueuePeek_sameWGStore p.txQueue)).wp Q)
    intro out
    rcases out with ⟨first, queue⟩
    apply preserves_bind
      ((modifyPeer_routing pid (fun p => {p with txQueue := queue}) (fun _ => rfl)).wp Q)
    intro _
    exact body first
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w)
    change routingView w = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem workerIter_routing (worker : Worker) (pid : Option Nat) (step afterItem : Leanux.M Bool)
    (hs : ProductRetainsRoutingCall step) (ha : ProductRetainsRoutingCall afterItem) :
    ProductRetainsRoutingCall (workerIter worker pid step afterItem) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have stepSpec : Preserves P step := RetainsRoutingCall.wp hs s
  have afterSpec : Preserves P afterItem := RetainsRoutingCall.wp ha s
  have main : Preserves P (workerIter worker pid step afterItem) := by
    routing_tx_source [workerIter] using [stepSpec, afterSpec]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem txIter_routing (pid : PeerId) (need : Leanux.M Bool) (hn : ProductRetainsRoutingCall need) :
    ProductRetainsRoutingCall (txIter pid need) := by
  apply workerIter_routing _ _ _ _ (RetainsRoutingCall.liftWG (txStep_routing pid))
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have needSpec : Preserves P need := RetainsRoutingCall.wp hn s
  have main : Preserves P (do branch .txNeedResched (← need)) := by
    routing_tx_source [] using [needSpec, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem xmitTrim_routing (pid : PeerId) : SameView routingView (xmitTrim pid) := by
  intro s
  let Q := fun t => t = s
  let P := fun w : WGWorld => Q (routingView w)
  have dropped : Preserves P (modifyDev fun d => {d with txDropped := d.txDropped + 1}) :=
    (modifyDev_routing (fun d => {d with txDropped := d.txDropped + 1}) (fun _ => rfl)).wp Q
  change Preserves P (xmitTrim pid)
  unfold xmitTrim
  apply preserves_bind ((getPeer_routing pid).wp Q)
  intro initial
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec routingView Q
    intro idx acc
    apply hoare_bind _ _ (routing_getPeer Q pid)
    intro p
    let R := fun w : WGWorld => Q (routingView w) ∧
      (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS)) R)
    intro trim
    cases trim <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hoare_consequence
        (preserves_pure (ForInStep.done PUnit.unit) : Preserves P (pure (ForInStep.done PUnit.unit) : WG.M (ForInStep PUnit)))
        (fun _ h => h.1) (fun _ _ h => h)
    · apply hoare_bind _ _ (routing_setPeer Q pid {p with staged := p.staged.drop 1})
      intro _
      exact preserves_bind dropped (fun _ => preserves_pure (ForInStep.yield PUnit.unit))
  · intro _
    exact preserves_pure ()

theorem xmitSplice_routing (pid : PeerId) (packets : List Packet) :
    SameView routingView (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_routing pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl)

/-- Original transmit entry retains routing data and surviving lists on every normal
return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_routing (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsRoutingCall (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi

  have lookupDstSpec : Preserves P (lookupDst family addr) := (lookupDst_routing family addr).wp Q
  have trim (pid : PeerId) : Preserves P (xmitTrim pid) := (xmitTrim_routing pid).wp Q
  have splice (pid : PeerId) (xs : List Packet) : Preserves P (xmitSplice pid xs) :=
    (xmitSplice_routing pid xs).wp Q
  have staged (pid : PeerId) : Preserves P (sendStagedPackets pid) :=
    RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have put (pid : Option PeerId) : Preserves P (peerPut pid) :=
    RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    (routing_kernel _ (loopbackSend_kernel sites raised)).wp Q
  have route {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have failure : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    (modifyDev_routing (fun d => {d with txErrors := d.txErrors + 1}) (fun _ => rfl)).wp Q
  have main : Preserves P (wgXmitSource family addr packets mtu) := by
    routing_tx_source [wgXmitSource] using [lookupDstSpec, trim, splice, staged, put, loopback, peer, failure, ambient, route]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem reply4_routing (dst : Nat) (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.Stack.reply4 dst bytes) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have route {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    productRouting_spec a (fun store => Q (store.2.2.2.dev.map routingState))
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView getDev
      (routing_kernel _ getDev_sameWGStore) (fun _ _ _ h => h)).wp Q
  have xmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (wgXmit_routing family addr packets mtu)) s
  have main : Preserves P (Leanux.Env.Stack.reply4 dst bytes) := by
    routing_tx_source [Leanux.Env.Stack.reply4] using [xmit, device, ambient, route]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem receive4_routing (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : ProductRetainsRoutingCall (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have excludedAlone (row : String) : ProductRetainsRoutingCall (Leanux.Env.Stack.excluded row) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : ProductRetainsRoutingCall
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    ProjectedRetainsRoutingCall.of_same ((liftWG_sameProductStore _ (liftRouting_sameWGStore _)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w => routingView w.wg) (fun _ => rfl))
  have read : ProductRetainsRoutingCall (getWG : Leanux.M WGWorld) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact RetainsRouting.refl _
  have write (f : EnvWorld → EnvWorld) : ProductRetainsRoutingCall (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact RetainsRouting.refl _
  have bindRule {α β : Type} {a : Leanux.M α} {f : α → Leanux.M β}
      (ha : ProductRetainsRoutingCall a) (hf : ∀ x, ProductRetainsRoutingCall (f x)) :
      ProductRetainsRoutingCall (a >>= f) := by
    intro initial
    apply hoare_consequence
      (preserves_bind (RetainsRoutingCall.wp ha initial) (fun x => RetainsRoutingCall.wp (hf x) initial))
    · intro w he
      change routingView w.wg = initial at he
      rw [he]
      exact RetainsRouting.refl _
    · intro _ _ h
      exact h
  have iteRule {α : Type} (p : Prop) [Decidable p] {a b : Leanux.M α}
      (ha : p → ProductRetainsRoutingCall a) (hb : ¬p → ProductRetainsRoutingCall b) :
      ProductRetainsRoutingCall (if p then a else b) := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  unfold ProductRetainsRoutingCall ProjectedRetainsRoutingCall
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (unfold ProductRetainsRoutingCall ProjectedRetainsRoutingCall)
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (rxstack_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (rxstack_head Leanux.Env.Stack.reply4; exact reply4_routing _ _)
    | (rxstack_head MonadLift.monadLift; exact route _ _)
    | (rxstack_head liftM; exact route _ _)
    | (rxstack_head getWG; exact read)
    | (rxstack_head modifyEnv; exact write _)
    | (rxstack_head Pure.pure; exact ProjectedRetainsRoutingCall.of_same (SameView.pure _ _))
    | (rxstack_head Bind.bind; refine bindRule ?_ ?_)
    | (rxstack_head ite; refine iteRule _ ?_ ?_)
    | keypairs_intro_forall
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_routing (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.deliverInner bytes) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have four : Preserves P (Leanux.Env.Stack.receive4 bytes) :=
    RetainsRoutingCall.wp (receive4_routing bytes) s
  have six : Preserves P (Leanux.Env.Stack.receive6 bytes) :=
    ((stackReceive6_sameKernel bytes).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w => routingView w.wg) (fun _ => rfl)).wp Q
  have main : Preserves P (Leanux.Env.deliverInner bytes) := by
    routing_tx_source [Leanux.Env.deliverInner, Leanux.Env.Stack.receive] using [four, six, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem stackForM_routing (packets : List (List UInt8)) :
    ProductRetainsRoutingCall (packets.forM Leanux.Env.deliverInner) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have main : Preserves P (packets.forM Leanux.Env.deliverInner) := by
    induction packets with
    | nil => simpa only [List.forM_eq_forM, List.forM_nil] using
        (preserves_pure PUnit.unit : Preserves P (pure PUnit.unit : Leanux.M PUnit))
    | cons bytes xs ih =>
      simpa only [List.forM_eq_forM, List.forM_cons] using
        preserves_bind (RetainsRoutingCall.wp (deliverInner_routing bytes) s) (fun _ => ih)
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem encryptPacket_routing (checksum : Packet → Leanux.M Packet)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    ProductRetainsRoutingCall (encryptPacket checksum key pkt) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView _
      ((calculateSkbPadding_sameWGWorld _ _).factor routingView) (fun _ _ _ h => h)).wp Q
  have checksumSpec (p : Packet) : Preserves P (checksum p) := RetainsRoutingCall.wp (hc p) s
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView _
      (getKeypair_routing key) (fun _ _ _ h => h)).wp Q
  have main : Preserves P (encryptPacket checksum key pkt) := by
    routing_tx_source [encryptPacket] using [padding, checksumSpec, keySpec, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem encryptPoll_routing : SameView routingView TxRing.pollSource := by
  intro s
  let Q : Option RoutingState → Prop := fun t => t = s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold P routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi

  have install (ring : PtrRing (List SkbId)) : Preserves P (modifyDev fun d => {d with encryptQueue := ring}) :=
    (modifyDev_routing (fun d => {d with encryptQueue := ring}) (fun _ => rfl)).wp Q
  change Preserves P TxRing.pollSource
  routing_tx_source [TxRing.pollSource] using [device, install]

theorem encryptStep_routing (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (hi : ProductRetainsRoutingCall softirq) :
    ProductRetainsRoutingCall (encryptStep checksum softirq) := by
  rw [← TxRing.stepSource_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have softirqSpec : Preserves P softirq := RetainsRoutingCall.wp hi s
  have poll : Preserves P (liftWG TxRing.pollSource) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView
      TxRing.pollSource encryptPoll_routing (fun _ _ _ h => h)).wp Q
  have nativeSkb {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have packet {α : Type} (a : SkbM α) : Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView _ (nativeSkb a) (fun _ _ _ h => h)).wp Q
  have encrypt (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket checksum key pkt) :=
    RetainsRoutingCall.wp (encryptPacket_routing checksum hc key pkt) s
  have enqueue (item : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx item state) : Leanux.M Unit) :=
    RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (enqueuePerPeerTx_routing item state)) s
  have main : Preserves P (TxRing.stepSource checksum softirq) := by
    routing_tx_source [TxRing.stepSource, getTxSkb, setTxSkb] using [softirqSpec, poll, packet, encrypt, enqueue, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem encryptIter_routing (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit) (need : Leanux.M Bool)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (hi : ProductRetainsRoutingCall softirq)
    (hn : ProductRetainsRoutingCall need) : ProductRetainsRoutingCall (encryptIter checksum softirq need) := by
  apply workerIter_routing _ _ _ _ (encryptStep_routing checksum softirq hc hi)
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)

  have needSpec : Preserves P need := RetainsRoutingCall.wp hn s
  have main : Preserves P (do branch .encWorkerNeedResched (← need)) := by
    routing_tx_source [] using [needSpec, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem actualChecksum_routing (pkt : Packet) : ProductRetainsRoutingCall (Leanux.Env.checksumHelp pkt) :=
  ProjectedRetainsRoutingCall.of_same
    ((checksumHelp_sameWorld pkt).of_factor
      (fun w : World => routingView w.wg)
      (fun w => routingView w.wg) (fun _ => rfl))

end Leanux.Proofs.WG.AllowedIps
