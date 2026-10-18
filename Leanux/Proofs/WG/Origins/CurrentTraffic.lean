import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.Origins.CurrentLifecycle
import Leanux.Proofs.WG.Queues.RxConsumeProtection

/-! Native traffic preserves configured and receipt-bound current identities.
The contracts concern actual normal endpoints; release may erase residents. -/
namespace Leanux.Proofs.WG.CurrentTraffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredHandshake ConfiguredReceive CurrentLifecycle

private theorem peerGet_view (pid : PeerId) : SameView ConfiguredIdentity.view (peerGet pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold peerGet
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,refcountInc,branch,branchCmp,unsupported]
  repeat' configured_step initial

private theorem keypairGet_view (kp : Option KeypairId) :
    SameView ConfiguredIdentity.view (keypairGet kp) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold keypairGet
  simp (config := {zeta := false}) only [refcountIncNotZero,branch,branchCmp,unsupported,invariant]
  repeat' first
    | (rx_retention_head getKeypair
       exact (ConfiguredIdentity.getKeypair_view _).wp (fun s => s = initial))
    | (rx_retention_head setKeypair
       exact (ConfiguredIdentity.setKeypair_view _ _).wp (fun s => s = initial))
    | configured_step initial

private theorem pay_preserves (history : List SessionOrigin.Receipt) (peer : Option PeerId) :
    Preserves (Inv history) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerPut_preserves peer)
      w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.peerPut_retains peer) w ambient result v ambient' hr)⟩

private theorem keyRead_preserves (history : List SessionOrigin.Receipt) (kid : KeypairId) :
    Preserves (Inv history) (getKeypair kid) :=
  current_preserves _ (ConfiguredIdentity.getKeypair_view kid)
    (Origins.Retaining.of_view (Origins.Retaining.getKeypair_material kid)) history

private theorem keyPut_preserves (history : List SessionOrigin.Receipt)
    (kp : Option KeypairId) (now : Bool) : Preserves (Inv history) (keypairPut kp now) :=
  current_preserves _ (ConfiguredIdentity.keypairPut_view kp now)
    (Origins.Retaining.keypairPut_material kp now) history

macro "current_traffic_step " history:term : tactic => `(tactic| first
  | (rx_retention_head peerGet
     exact current_preserves _ (peerGet_view _)
       (Origins.Retaining.of_view (Origins.Retaining.peerGet_material _)) $history)
  | (rx_retention_head peerPut; exact pay_preserves $history _)
  | (rx_retention_head keypairGet
     exact current_preserves _ (keypairGet_view _)
       (Origins.Retaining.keypairGet_material _) $history)
  | (rx_retention_head keypairPut; exact keyPut_preserves $history _ _)
  | (rx_retention_head getKeypair; exact keyRead_preserves $history _)
  | (rx_retention_head branchExpired
     exact (branchExpired_sameWGWorld _ _ _ _).wp (Inv $history))
  | (rx_retention_head IndexOwner.peerDeref
     exact indexOwner_peerDeref_preserves _ (Inv $history))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Inv $history)
     intro x b
     change Preserves (Inv $history) _)
  | receive_basic $history with (Inv $history)
  | current_lifecycle_step $history)

theorem sendQueuedHandshakeInitiation_preserves (pid : PeerId) (retry : Bool)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' current_traffic_step history

private theorem receivedWithKeypair_view (pid : PeerId) (kid : KeypairId) :
    SameView ConfiguredIdentity.view (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keypairPut
       exact (ConfiguredIdentity.keypairPut_view _ _).wp (fun s => s = initial))
    | configured_step initial

theorem receivedWithKeypair_preserves (pid : PeerId) (kid : KeypairId)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (receivedWithKeypair pid kid) :=
  current_preserves _ (receivedWithKeypair_view pid kid)
    (Origins.Retaining.receivedWithKeypair_material pid kid) history

theorem keepKeyFreshRx_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact sendQueuedHandshakeInitiation_preserves _ _ history)
    | current_traffic_step history


theorem readPeer_spec (history : List SessionOrigin.Receipt) (pid : PeerId) :
    Hoare (getPeer pid) (Inv history) (fun p w => Inv history w ∧
      (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hi hr
  have eq := (Peers.getPeer_current pid w v p ambient ambient' hr).1
  exact ⟨eq ▸ hi, ((hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.getPeer_spec (fun _ => True) pid) w ambient p v ambient' trivial hr).2⟩

theorem writePeer_spec (history : List SessionOrigin.Receipt) (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p) (fun w => Inv history w ∧
      (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p))
      (fun _ => Inv history) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have eq := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.setPeer_spec (fun s => s = ConfiguredIdentity.view w) pid p)
      w ambient result v ambient' ⟨rfl,hi.2⟩ hr
  constructor
  · intro state hs
    exact hi.1.1 state (eq.symm.trans hs)
  · exact hi.1.2.retain (CurrentIdentity.retains_of_configured_view
      ((ProjectedAction.iff_run_ambient _ _ _).mp
        (Origins.Retaining.of_view (Origins.setPeer_view pid p))
        w ambient result v ambient' hr) eq)

private theorem skb_preserves {α : Type} (a : SkbM α) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (liftSkb a) := by
  apply current_preserves
  · intro initial
    apply hoare_liftSkb
    intro w d store hi hd
    simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi
  · apply Origins.Retaining.of_view
    intro initial
    apply hoare_liftSkb
    intro w d store hi hd
    simpa only [Origins.view,id,hd,Option.map_some] using hi

macro "current_skb_step " history:term : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb; exact skb_preserves _ $history))

private theorem cpumaskChooseOnline_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec ConfiguredIdentity.view (fun s => s = initial)
       intro x b
       change Preserves (fun w => ConfiguredIdentity.view w = initial) _)
    | configured_step initial

private theorem enqueuePerDeviceAndPeer_view (pid : PeerId) (item : List SkbId) :
    SameView ConfiguredIdentity.view (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,setTxSkb,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head liftSkb
       apply hoare_liftSkb
       intro w d store hi hd
       simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi)
    | (rx_retention_head cpumaskNextOnlineFrom
       exact (ConfiguredIdentity.sameWG (project := id) (cpumaskNextOnlineFrom_sameStore _)).wp
         (fun s => s = initial))
    | configured_step initial

private theorem enqueuePerPeerTx_preserves (item : List SkbId) (state : PacketState)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline
       exact current_preserves _ (cpumaskChooseOnline_view _)
         (Origins.Retaining.of_view (Origins.Retaining.cpumaskChooseOnline_material _)) history)
    | current_skb_step history
    | current_traffic_step history

private theorem createData_preserves (pid : PeerId) (item : List SkbId)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer
       exact current_preserves _ (enqueuePerDeviceAndPeer_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.enqueuePerDeviceAndPeer_material _ _)) history)
    | (rx_retention_head enqueuePerPeerTx; exact enqueuePerPeerTx_preserves _ _ history)
    | current_skb_step history
    | current_traffic_step history


private theorem keyUpdateThen_preserves {α : Type} (history : List SessionOrigin.Receipt)
    (kid : KeypairId) (f : Keypair → Keypair)
    (valid : ∀ k, (f k).receiving.isValid = true → k.receiving.isValid = true)
    (keep : ∀ k, Origins.KeyLe (f k) k) (next : Keypair → WG.M α)
    (hn : ∀ k, Preserves (Inv history) (next k)) :
    Preserves (Inv history) (do let k ← getKeypair kid; setKeypair kid (f k); next k) := by
  let update : WG.M Keypair := do
    let k ← getKeypair kid
    setKeypair kid (f k)
    pure k
  have configured : SameView ConfiguredIdentity.view update := by
    apply SameView.bind (ConfiguredIdentity.getKeypair_view kid)
    intro k
    apply SameView.bind (ConfiguredIdentity.setKeypair_view kid (f k))
    intro _
    exact SameView.pure _ k
  have material : Origins.Retaining.RetainsCall update := by
    intro initial
    apply hoare_consequence
      ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.keyUpdateThen_material)
        initial kid f valid keep (fun k => pure k) (fun k => preserves_pure k))
    · intro w hw
      change Origins.view w = initial at hw
      rw [hw]
      exact Origins.RetainsView.refl _
    · exact fun _ _ h => h
  have h := preserves_bind (current_preserves update configured material history) hn
  change Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w) _
  simpa only [update,bind_assoc,pure_bind] using h

private theorem keyUpdate_preserves (history : List SessionOrigin.Receipt)
    (kid : KeypairId) (f : Keypair → Keypair)
    (valid : ∀ k, (f k).receiving.isValid = true → k.receiving.isValid = true)
    (keep : ∀ k, Origins.KeyLe (f k) k) :
    Preserves (Inv history) (getKeypair kid >>= fun k => setKeypair kid (f k)) := by
  have h := keyUpdateThen_preserves history kid f valid keep (fun _ => pure ())
    (fun _ => preserves_pure ())
  simpa only [bind_pure_unit] using h

open Lean Meta Elab Tactic in
elab "current_key_update_head " wanted:ident : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOf ``Preserves do throwError "not a preservation contract"
  let .app _ action := t | throwError "missing action"
  let action := action.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  unless args.size ≥ 2 do throwError "missing bind operands"
  unless args[args.size-2]!.consumeMData.isAppOf ``getKeypair do throwError "not a key read"
  let .lam _ _ body _ := args.back!.consumeMData | throwError "not a continuation"
  let rec head : Nat → Expr → Expr
    | 0, e => e.consumeMData
    | n+1, e => match e.consumeMData with
      | .letE _ _ value rest _ => head n (rest.instantiate1 value)
      | e => e.headBeta
  let body := head 16 body
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless body.isAppOf expected do throwError "different next action"
  if expected == ``Bind.bind then
    let next := body.getAppArgs
    unless next.size ≥ 2 do throwError "missing write bind operands"
    unless next[next.size-2]!.consumeMData.isAppOf ``setKeypair do throwError "not a key write"

macro "current_key_update " history:term : tactic => `(tactic| first
  | (current_key_update_head setKeypair
     apply keyUpdate_preserves $history
     · intro k valid; exact valid
     · intro k; exact ⟨rfl,Or.inr rfl⟩)
  | (current_key_update_head Bind.bind
     apply keyUpdateThen_preserves $history
     · intro k valid; exact valid
     · intro k; exact ⟨rfl,Or.inr rfl⟩
     intro k))

private theorem restoreStaged_preserves (pid : PeerId) (packets : List Packet)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (do
      setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }) := by
  apply current_preserves
  · intro initial
    change Preserves (fun w => ConfiguredIdentity.view w = initial) _
    repeat' configured_step initial
  · apply Origins.Retaining.of_view
    intro initial
    change Preserves (fun w => Origins.view w = initial) _
    repeat' first
      | (rx_retention_head getPeer; exact (Origins.getPeer_view _).wp (fun s => s = initial))
      | (rx_retention_head setPeer; exact (Origins.setPeer_view _ _).wp (fun s => s = initial))
      | rx_retention_step

private theorem stagedOutNokey_preserves (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (stagedOutNokey pid packets keypair invalid) := by
  have restore := restoreStaged_preserves pid packets history
  have factor : stagedOutNokey pid packets keypair invalid = (do
      if invalid then
        let some id := keypair | invariant "unreachable"
        let k ← getKeypair id
        setKeypair id {k with sending := {k.sending with isValid := false}}
      keypairPut keypair false
      for _ in packets do _ ← branch .stagedOrphanWalk true
      _ ← branch .stagedOrphanWalk false
      (do setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged })
      sendQueuedHandshakeInitiation pid false) := by
    cases invalid <;> cases keypair <;>
      simp only [stagedOutNokey,Bool.false_eq_true,ite_false,ite_true,bind_assoc]
  rw [factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer; exact restore)
    | current_key_update history
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact sendQueuedHandshakeInitiation_preserves _ _ history)
    | current_traffic_step history


private theorem stagedSubmit_preserves (pid kid : Nat) (packets : List DataPacket)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (RxCredits.stagedSubmit pid kid packets) := by
  unfold RxCredits.stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact createData_preserves _ _ history)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id (Inv history)
       intro packet
       change Preserves (Inv history) _)
    | current_skb_step history
    | current_traffic_step history

private theorem stagedKeySource_preserves (pid kid : Nat) (packets : List Packet)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (RxCredits.stagedKeySource pid kid packets) := by
  unfold RxCredits.stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | current_key_update history
    | (rx_retention_head stagedOutNokey; exact stagedOutNokey_preserves _ _ _ _ history)
    | (rx_retention_head RxCredits.stagedSubmit; exact stagedSubmit_preserves _ _ _ history)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (Inv history))
    | current_traffic_step history

theorem sendStagedPackets_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (sendStagedPackets pid) := by
  rw [← RxCredits.stagedFullSource_eq]
  unfold RxCredits.stagedFullSource
  apply hoare_bind _ _ (readPeer_spec history pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true =>
    exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (writePeer_spec history pid {p with staged := []})
    intro _
    change Preserves (Inv history) _
    simp (config := {zeta := false}) only [branch,invariant]
    repeat' first
      | (rx_retention_head stagedOutNokey; exact stagedOutNokey_preserves _ _ _ _ history)
      | (rx_retention_head RxCredits.stagedKeySource; exact stagedKeySource_preserves _ _ _ history)
      | current_traffic_step history

theorem sendKeepalive_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (sendKeepalive pid) := by
  unfold sendKeepalive
  apply hoare_bind _ _ (readPeer_spec history pid)
  intro p
  let P := fun w => Inv history w ∧
    (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) P)
  intro empty
  cases empty with
  | false =>
    change Hoare (sendStagedPackets pid) P (fun _ => Inv history)
    exact hoare_consequence (sendStagedPackets_preserves pid history)
      (fun _ h => h.1) (fun _ _ h => h)
  | true =>
    dsimp only
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) P)
    intro allocated
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keepaliveNoMem (!allocated)) P)
    intro absent
    cases absent with
    | true =>
      exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
    | false =>
      have getter : Preserves P getDev := by
        unfold getDev
        simp only [invariant]
        repeat' first
          | (rx_retention_head get; exact hoare_consequence (hoare_get P)
              (fun _ h => h) (fun _ _ h => h.2))
          | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
          | rx_retention_step
      apply hoare_bind _ _ getter
      intro d
      apply hoare_bind _ _ (writePeer_spec history pid {p with staged := p.staged ++ [{mtu := d.mtu}]})
      intro _
      exact sendStagedPackets_preserves pid history


/-- Cookie lookup can clear an owner word and its final payment can erase a
peer. Preserve the two conditional identity invariants through those effects. -/
theorem cookieMessageConsume_preserves (msg : List UInt8)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (cookieMessageConsume msg) := by
  have lookup (kinds : List IndexKind) (index : Nat) :
      Preserves (Inv history) (indexLookup kinds index) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.indexLookup_preserves kinds index)
        w ambient result v ambient' hi.1 hr,
      hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
        (CurrentIdentity.indexLookup_current kinds index) w ambient result v ambient' hr)⟩
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup _ _)
    | current_traffic_step history

end Leanux.Proofs.WG.CurrentTraffic
