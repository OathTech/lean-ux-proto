import Leanux.Proofs.WG.Lifetimes.HandshakeConstruct

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Complete original Noise consumption. Reference-taking lookups and every
failure put are observed, as are all fresh peer accesses after authentication.
These contracts concern resolved identities, not cryptographic validity or
ownership of the table's scalar references. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do


private theorem consume_ite_contract {α : Sort u} (P : α → Prop)
    (p : Prop) [Decidable p] (yes no : α) (hy : P yes) (hn : P no) :
    P (if p then yes else no) := by
  split <;> assumption

private theorem consume_ite_relation {α : Sort u} {β : Sort v} (R : α → β → Prop)
    (p : Prop) [Decidable p] (yes no : α) (yes' no' : β)
    (hy : R yes yes') (hn : R no no') :
    R (if p then yes else no) (if p then yes' else no') := by
  split <;> assumption

/-- Split only the source's leading conditional; do not simplify its continuation. -/
elab "consume_conditional" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let .app (.app front observed) post := target | Lean.throwError "missing observer contract"
  let product := observed.isAppOf ``liftWGObserver
  let action := if product then observed.getAppArgs.back!.consumeMData else observed.consumeMData
  unless action.isAppOf ``ite do Lean.throwError "not a leading conditional"
  let args := action.getAppArgs
  unless args.size == 5 do Lean.throwError "malformed conditional"
  let p := args[1]!
  let yes := args[3]!
  let no := args[4]!
  if target.isAppOf ``ErasesStatePrefix then
    unless post.isAppOf ``ite do Lean.throwError "not paired conditionals"
    let rhs := post.getAppArgs
    unless rhs.size == 5 do Lean.throwError "malformed source conditional"
    unless ← Lean.Meta.isDefEq p rhs[1]! do Lean.throwError "different conditions"
    let hy ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (Lean.mkApp2 front yes rhs[3]!)
    let hn ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (Lean.mkApp2 front no rhs[4]!)
    let proof ← Lean.Meta.mkAppM ``consume_ite_relation #[front, p, yes, no, rhs[3]!, rhs[4]!, hy, hn]
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal [hy.mvarId!, hn.mvarId!]
  else
    let wrap (a : Lean.Expr) :=
      if product then Lean.mkApp observed.appFn! a else a
    let property ← Lean.Meta.withLocalDeclD `action (← Lean.Meta.inferType yes) fun a =>
      Lean.Meta.mkLambdaFVars #[a] (Lean.mkApp2 front (wrap a) post)
    let hy ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ((Lean.mkApp property yes).headBeta)
    let hn ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ((Lean.mkApp property no).headBeta)
    let proof ← Lean.Meta.mkAppM ``consume_ite_contract #[property, p, yes, no, hy, hn]
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal [hy.mvarId!, hn.mvarId!]


private theorem consume_erases_bind_associated {α β γ : Type}
    {g : MixedM α} {f : α → MixedM β} {tail : β → MixedM γ}
    {a : WG.M α} {b : α → WG.M β} {suffix : β → WG.M γ}
    (hg : ErasesStatePrefix g a) (hf : ∀ x, ErasesStatePrefix (f x) (b x))
    (ht : ∀ y, ErasesStatePrefix (tail y) (suffix y)) :
    ErasesStatePrefix ((g >>= f) >>= tail) (a >>= fun x => b x >>= suffix) := by
  rw [bind_assoc]
  exact erasesStatePrefix_bind hg (fun x => erasesStatePrefix_bind (hf x) ht)

elab "consume_erases_modify_bind" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``ErasesStatePrefix do Lean.throwError "not an erasure"
  let args := target.getAppArgs
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let bindArgs := action.getAppArgs
  unless bindArgs.size ≥ 2 && bindArgs[bindArgs.size - 2]!.isAppOf ``modifyPeerKeysPrefix do
    Lean.throwError "not a peer update bind"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply consume_erases_bind_associated))

def consumeInitiationPrefix (msg : List UInt8) : MixedM (Option PeerId) := do
  let out (peer : Option PeerId) (ret : Option PeerId) : MixedM (Option PeerId) := do
    if ← liftWGPrefix (branch .consumeFailedPut ret.isNone) then peerPutMixed peer
    return ret
  let identity := (← liftWGPrefix getDev).staticIdentity
  if ← liftWGPrefix (branch .consumeNoIdentity !identity.hasIdentity) then return ← out none none
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← liftWGPrefix (messageEphemeral true e handshakeInitChainingKey hash)
  let es ← liftWGPrefix (mixDh true ck identity.staticPrivate e)
  if ← liftWGPrefix (branch .consumeEsFailed es.isNone) then return ← out none none
  let some (ck, key) := es | liftWGPrefix (invariant "unreachable")
  let st ← liftWGPrefix (messageDecrypt ((msg.drop 40).take 48) key hash)
  if ← liftWGPrefix (branch .consumeStaticFailed st.isNone) then return ← out none none
  let some (s, hash) := st | liftWGPrefix (invariant "unreachable")
  let peer ← pubkeyLookupPrefix s
  if ← liftWGPrefix (branch .consumeNoPeer peer.isNone) then return ← out none none
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  let ss ← liftWGPrefix (mixPrecomputedDh ck (← getPeerMixed pid).precomputedStaticStatic)
  if ← liftWGPrefix (branch .consumeSsFailed ss.isNone) then return ← out peer none
  let some (ckSs, key) := ss | liftWGPrefix (invariant "unreachable")
  let ts ← liftWGPrefix (messageDecrypt ((msg.drop 88).take 28) key hash)
  if ← liftWGPrefix (branch .consumeTimestampFailed ts.isNone) then return ← out peer none
  let some (t, hashT) := ts | liftWGPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← liftWGPrefix (hiddenClock64 .floodNow)
  if ← liftWGPrefix (WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt)) then
    return ← out peer none
  modifyPeerKeysPrefix pid fun p => {p with remoteEphemeral := e}
  if ← liftWGPrefix (branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt)) then
    modifyPeerKeysPrefix pid fun p => {p with latestTimestamp := t}
  modifyPeerKeysPrefix pid fun p => {p with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4}
  let consumption ← liftWGPrefix (hiddenClock64 .consumptionNow)
  let last := (← getPeerMixed pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← liftWGPrefix (branchCmp .consumeLaterTime (diff < 0) diff.toInt 0) then
    modifyPeerKeysPrefix pid fun p => {p with lastInitiationConsumption := consumption}
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}
  out peer (some pid)

/-- Literal source continuation after the checked handshake-owner match. -/
private def consumeResponseTail (msg : List UInt8) (identity : StaticIdentity)
    (pid : PeerId) : WG.M (Option PeerId) := do
  let fail : WG.M (Option PeerId) := do
    peerPut (some pid)
    return none
  let p ← getPeer pid
  let state := p.handshakeState
  if ← branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck, h) ← messageEphemeral true eph p.chainingKey p.hash
  let ee ← mixDh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck, _) := ee | invariant "unreachable"
  let se ← mixDh false ck identity.staticPrivate eph
  if ← branch .crespSeFailed se.isNone then return ← fail
  let some (ck, _) := se | invariant "unreachable"
  let outs ← kdf true true ck p.presharedKey
  let (ck, tempHash, key) := (← kdfOut outs 0, ← kdfOut outs 1, ← kdfOut outs 2)
  let h := noiseHash (h ++ tempHash)
  let dec ← messageDecrypt ((msg.drop 44).take 16) key h
  if ← branch .crespDecryptFailed dec.isNone then return ← fail
  let some (_, h) := dec | invariant "unreachable"
  if ← branch .crespStateChanged ((← getPeer pid).handshakeState != state) then return ← fail
  setPeer pid { (← getPeer pid) with remoteEphemeral := eph, hash := h, chainingKey := ck,
                                     remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE }
  return some pid

/-- The same continuation, observing each actual peer access. -/
private def consumeResponseTailPrefix (msg : List UInt8) (identity : StaticIdentity)
    (pid : PeerId) : MixedM (Option PeerId) := do
  let fail : MixedM (Option PeerId) := do
    peerPutMixed (some pid)
    return none
  let p ← getPeerMixed pid
  let state := p.handshakeState
  if ← liftWGPrefix (branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION)) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck, h) ← liftWGPrefix (messageEphemeral true eph p.chainingKey p.hash)
  let ee ← liftWGPrefix (mixDh false ck p.ephemeralPrivate eph)
  if ← liftWGPrefix (branch .crespEeFailed ee.isNone) then return ← fail
  let some (ck, _) := ee | liftWGPrefix (invariant "unreachable")
  let se ← liftWGPrefix (mixDh false ck identity.staticPrivate eph)
  if ← liftWGPrefix (branch .crespSeFailed se.isNone) then return ← fail
  let some (ck, _) := se | liftWGPrefix (invariant "unreachable")
  let outs ← liftWGPrefix (kdf true true ck p.presharedKey)
  let (ck, tempHash, key) := (← liftWGPrefix (kdfOut outs 0), ← liftWGPrefix (kdfOut outs 1), ← liftWGPrefix (kdfOut outs 2))
  let h := noiseHash (h ++ tempHash)
  let dec ← liftWGPrefix (messageDecrypt ((msg.drop 44).take 16) key h)
  if ← liftWGPrefix (branch .crespDecryptFailed dec.isNone) then return ← fail
  let some (_, h) := dec | liftWGPrefix (invariant "unreachable")
  if ← liftWGPrefix (branch .crespStateChanged ((← getPeerMixed pid).handshakeState != state)) then return ← fail
  modifyPeerKeysPrefix pid fun p => {p with remoteEphemeral := eph, hash := h, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE}
  return some pid

private theorem consumeResponse_factor (msg : List UInt8) :
    consumeResponse msg = (do
      let identity := (← getDev).staticIdentity
      if ← branch .crespNoIdentity !identity.hasIdentity then return none
      let entry ← indexLookup [.handshake] (u32le msg 8)
      if ← branch .crespNoHandshake entry.isNone then return none
      let some (IndexOwner.handshake _, pid) := entry |
        invariant "a keypair entry under the handshake mask"
      consumeResponseTail msg identity pid) := by
  rfl

def consumeResponsePrefix (msg : List UInt8) : MixedM (Option PeerId) := do
  let identity := (← liftWGPrefix getDev).staticIdentity
  if ← liftWGPrefix (branch .crespNoIdentity !identity.hasIdentity) then return none
  let entry ← indexLookupPrefix [.handshake] (u32le msg 8)
  if ← liftWGPrefix (branch .crespNoHandshake entry.isNone) then return none
  let some (IndexOwner.handshake _, pid) := entry | liftWGPrefix (invariant "a keypair entry under the handshake mask")
  consumeResponseTailPrefix msg identity pid

private theorem consumeResponseTailPrefix_erases (msg : List UInt8)
    (identity : StaticIdentity) (pid : PeerId) :
    ErasesStatePrefix (consumeResponseTailPrefix msg identity pid) (consumeResponseTail msg identity pid) := by
  delta consumeResponseTailPrefix consumeResponseTail
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head indexLookupPrefix; exact indexLookupPrefix_erases _ _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

private theorem consumeResponseTailPrefix_preserves (c : AmbientContracts I) (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeResponseTailPrefix msg identity pid) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (Leanux.branch d b)) :=
    ambient (AmbientM.branch d b)
  have comparison_spec (d : Decision) (b : Bool) (lhs rhs : Int) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (Leanux.branchCmp d b lhs rhs)) :=
    ambient (AmbientM.branchCmp d b lhs rhs)
  change StatePrefixEnsures _ _ _ (fun _ h w _ => I h w)
  delta consumeResponseTailPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head indexLookupPrefix; exact indexLookupPrefix_preserves_ambient c _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; exact ambient (AmbientM.hiddenClock64 _))
    | (maintenance_lift_action_head messageEphemeral; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head messageDecrypt; exact whole _ (Framing.messageDecrypt_sameWGWorld _ _ _))
    | (maintenance_lift_action_head kdf; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_lift_action_head branch; exact branch_spec _ _)
    | (maintenance_lift_action_head branchCmp; exact comparison_spec _ _ _ _)
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head liftWGPrefix; first | exact branch_spec _ _ | exact comparison_spec _ _ _ _ | exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

private theorem consumeResponseTailPrefix_preserves_product (c : ProductAmbientContracts I) (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeResponseTailPrefix msg identity pid)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (Leanux.branch d b))) :=
    ambient (AmbientM.branch d b)
  have comparison_spec (d : Decision) (b : Bool) (lhs rhs : Int) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (Leanux.branchCmp d b lhs rhs))) :=
    ambient (AmbientM.branchCmp d b lhs rhs)
  apply PrefixEnsures.preserves
  delta consumeResponseTailPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head pubkeyLookupPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head indexLookupPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact indexLookupPrefix_preserves_product c _ _)
    | (maintenance_head peerPutMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact c.peerPut _)
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.hiddenClock64 _))
    | (maintenance_lift_action_head messageEphemeral; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head messageDecrypt; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageDecrypt_sameWGWorld _ _ _))
    | (maintenance_lift_action_head kdf; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_lift_action_head branch; change PrefixPreserves I LifetimeEvent.Safe _; exact branch_spec _ _)
    | (maintenance_lift_action_head branchCmp; change PrefixPreserves I LifetimeEvent.Safe _; exact comparison_spec _ _ _ _)
    | (maintenance_lift_action_head invariant; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.invariant _))
    | (maintenance_head liftWGPrefix; first | exact branch_spec _ _ | exact comparison_spec _ _ _ _ | exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem consumeInitiationPrefix_erases (msg : List UInt8) :
    ErasesStatePrefix (consumeInitiationPrefix msg) (consumeInitiation msg) := by
  unfold consumeInitiationPrefix consumeInitiation
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_erases _)
    | (maintenance_head indexLookupPrefix; exact indexLookupPrefix_erases _ _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem consumeResponsePrefix_erases (msg : List UInt8) :
    ErasesStatePrefix (consumeResponsePrefix msg) (consumeResponse msg) := by
  apply Eq.mpr (congrArg (fun original => ErasesStatePrefix (consumeResponsePrefix msg) original)
    (consumeResponse_factor msg))
  delta consumeResponsePrefix
  apply erasesStatePrefix_bind (erasesStatePrefix_lift getDev)
  intro d
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro noIdentity
  cases noIdentity with
  | true => exact erasesStatePrefix_pure none
  | false =>
    apply erasesStatePrefix_bind (indexLookupPrefix_erases _ _)
    intro entry
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro noHandshake
    cases noHandshake with
    | true => exact erasesStatePrefix_pure none
    | false =>
      cases entry with
      | none => exact erasesStatePrefix_lift _
      | some pair =>
        rcases pair with ⟨owner, pid⟩
        cases owner with
        | handshake peer => exact consumeResponseTailPrefix_erases msg d.staticIdentity pid
        | keypair kp => exact erasesStatePrefix_lift _

theorem consumeInitiationPrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeInitiationPrefix msg) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (Leanux.branch d b)) :=
    ambient (AmbientM.branch d b)
  have comparison_spec (d : Decision) (b : Bool) (lhs rhs : Int) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (Leanux.branchCmp d b lhs rhs)) :=
    ambient (AmbientM.branchCmp d b lhs rhs)
  have reject (replay : Bool) (lhs now : Int64) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (WG.orM (branch .consumeReplay replay) (branchCmp .consumeFlood (lhs > now) lhs.toInt now.toInt))) := by
    apply store
    apply orM_sameView
    · intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) _
    · intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _
  have dev : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix getDev) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  change StatePrefixEnsures _ _ _ (fun _ h w _ => I h w)
  unfold consumeInitiationPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_preserves_ambient c _)
    | (maintenance_head indexLookupPrefix; exact indexLookupPrefix_preserves_ambient c _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; exact dev)
    | (maintenance_lift_action_head hiddenClock64; exact ambient (AmbientM.hiddenClock64 _))
    | (maintenance_lift_action_head WG.orM; exact reject _ _ _)
    | (maintenance_lift_action_head messageEphemeral; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head messageDecrypt; exact whole _ (Framing.messageDecrypt_sameWGWorld _ _ _))
    | (maintenance_lift_action_head kdf; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_lift_action_head branch; exact branch_spec _ _)
    | (maintenance_lift_action_head branchCmp; exact comparison_spec _ _ _ _)
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head liftWGPrefix; first | exact branch_spec _ _ | exact comparison_spec _ _ _ _ | exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem consumeResponsePrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeResponsePrefix msg) := by
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    AmbientContracts.drop (c.store (fun _ => True) _ (by intro initial; exact hoare_liftAmbient a _))
  have dev : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix getDev) := by
    apply AmbientContracts.drop (c.store (fun _ => True) getDev _)
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  have done : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (pure (none : Option PeerId) : MixedM (Option PeerId)) :=
    StatePrefixEnsures.pure none (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  change StatePrefixEnsures _ _ _ (fun _ h w _ => I h w)
  delta consumeResponsePrefix
  apply StatePrefixEnsures.bind dev
  intro d
  apply StatePrefixEnsures.bind (ambient (AmbientM.branch .crespNoIdentity !d.staticIdentity.hasIdentity))
  intro noIdentity
  cases noIdentity with
  | true => exact done
  | false =>
    apply StatePrefixEnsures.bind (indexLookupPrefix_preserves_ambient c _ _)
    intro entry
    apply StatePrefixEnsures.bind (ambient (AmbientM.branch .crespNoHandshake entry.isNone))
    intro noHandshake
    cases noHandshake with
    | true => exact done
    | false =>
      cases entry with
      | none => exact ambient (AmbientM.invariant _)
      | some pair =>
        rcases pair with ⟨owner, pid⟩
        cases owner with
        | handshake peer => exact consumeResponseTailPrefix_preserves c msg d.staticIdentity pid
        | keypair kp => exact ambient (AmbientM.invariant _)


theorem consumeInitiationPrefix_preserves_product (c : ProductAmbientContracts I) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeInitiationPrefix msg)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (Leanux.branch d b))) :=
    ambient (AmbientM.branch d b)
  have comparison_spec (d : Decision) (b : Bool) (lhs rhs : Int) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (Leanux.branchCmp d b lhs rhs))) :=
    ambient (AmbientM.branchCmp d b lhs rhs)
  have reject (replay : Bool) (lhs now : Int64) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (WG.orM (branch .consumeReplay replay) (branchCmp .consumeFlood (lhs > now) lhs.toInt now.toInt)))) := by
    apply store
    apply orM_sameView
    · intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) _
    · intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _
  have dev : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix getDev)) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  apply PrefixEnsures.preserves
  unfold consumeInitiationPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head pubkeyLookupPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact pubkeyLookupPrefix_preserves_product c _)
    | (maintenance_head indexLookupPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact indexLookupPrefix_preserves_product c _ _)
    | (maintenance_head peerPutMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact c.peerPut _)
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; change PrefixPreserves I LifetimeEvent.Safe _; exact dev)
    | (maintenance_lift_action_head hiddenClock64; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.hiddenClock64 _))
    | (maintenance_lift_action_head WG.orM; change PrefixPreserves I LifetimeEvent.Safe _; exact reject _ _ _)
    | (maintenance_lift_action_head messageEphemeral; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head messageDecrypt; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageDecrypt_sameWGWorld _ _ _))
    | (maintenance_lift_action_head kdf; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_lift_action_head branch; change PrefixPreserves I LifetimeEvent.Safe _; exact branch_spec _ _)
    | (maintenance_lift_action_head branchCmp; change PrefixPreserves I LifetimeEvent.Safe _; exact comparison_spec _ _ _ _)
    | (maintenance_lift_action_head invariant; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.invariant _))
    | (maintenance_head liftWGPrefix; first | exact branch_spec _ _ | exact comparison_spec _ _ _ _ | exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem consumeResponsePrefix_preserves_product (c : ProductAmbientContracts I) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeResponsePrefix msg)) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (by intro initial; exact hoare_liftAmbient a _))
  have dev : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix getDev)) := by
    apply ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev _)
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  have done : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (pure (none : Option PeerId) : MixedM (Option PeerId))) := by
    rw [liftWGObserver_pure]
    exact PrefixPreserves.pure c.safe none
  delta consumeResponsePrefix
  rw [liftWGObserver_bind]
  apply PrefixPreserves.bind dev
  intro d
  rw [liftWGObserver_bind]
  apply PrefixPreserves.bind (ambient (AmbientM.branch .crespNoIdentity !d.staticIdentity.hasIdentity))
  intro noIdentity
  cases noIdentity with
  | true => exact done
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [liftWGObserver_bind]
    apply PrefixPreserves.bind (indexLookupPrefix_preserves_product c _ _)
    intro entry
    rw [liftWGObserver_bind]
    apply PrefixPreserves.bind (ambient (AmbientM.branch .crespNoHandshake entry.isNone))
    intro noHandshake
    cases noHandshake with
    | true => exact done
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases entry with
      | none => exact ambient (AmbientM.invariant _)
      | some pair =>
        rcases pair with ⟨owner, pid⟩
        cases owner with
        | handshake peer => exact consumeResponseTailPrefix_preserves_product c msg d.staticIdentity pid
        | keypair kp => exact ambient (AmbientM.invariant _)


end Leanux.Proofs.WG.Lifetimes
