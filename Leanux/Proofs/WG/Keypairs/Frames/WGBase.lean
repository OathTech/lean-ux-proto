import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.WG.Keypairs.Frames.Tools
import Leanux.Proofs.WG.Peers.Primitives
import Leanux.Proofs.WG.Keypairs.SnapshotRules
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.Framing.WGConfiguration

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Receive-state contracts for the unchanged WireGuard state, queue, trie,
peer and socket helpers. Ordinary keypair allocation/deletion is separate. -/
namespace Leanux.Proofs.WG.Keypairs.WGFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs

open Lean Meta Elab Tactic

macro "snapshot_pinned_head " n:ident : tactic => do
  pure (← `(tactic| snapshot_head $(Lean.mkCIdent (Framing.normalizePinnedName n.getId))))

private def snapshotHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE name _ v b _ =>
      if name.toString.startsWith "__do_jp" then e
      else snapshotHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE name _ v b _ =>
        if name.toString.startsWith "__do_jp" then e
        else snapshotHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else snapshotHeadBZ n e'
      | _ => e

elab "snapshot_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameSnapshot || t.isAppOf ``Framing.SameView do throwError "not SameSnapshot"
  let .app f a := t | throwError "missing action"
  let a' := snapshotHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "snapshot_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameSnapshot || t.isAppOf ``Framing.SameView do throwError "not SameSnapshot"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)


/-- Prove each compiler-generated continuation once, then use its contract. -/
elab "snapshot_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameSnapshot || target.isAppOf ``Framing.SameView do throwError "not SameSnapshot"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``SameSnapshot #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``SameSnapshot #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `snapshot_join contract fun hf => do
      let bodyProp ← mkAppM ``SameSnapshot #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "snapshot_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameSnapshot || target.isAppOf ``Framing.SameView do throwError "not SameSnapshot"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `snapshot_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"


/-- Apply an existing frame only when its source action head matches. -/
elab "snapshot_fact " n:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameSnapshot || target.isAppOf ``Framing.SameView do
    throwError "not a snapshot frame"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let proof ← mkConstWithFreshMVarLevels name
  let (_, _, conclusion) ← forallMetaTelescope (← inferType proof)
  unless conclusion.isAppOf ``SameSnapshot || conclusion.isAppOf ``Framing.SameView do
    throwError "not a frame theorem"
  let framed := conclusion.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn == framed.getAppFn do throwError "different source action"
  replaceMainGoal (← goal.apply proof)

/-- Compose the actual source with canonical component rules and named frames.
No verification-condition engine or alternate execution stack is introduced. -/
macro "snapshot_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let pinned := fs.getElems.map fun f =>
    if f.getId.toString.startsWith "_private." then
      Lean.mkCIdent (Framing.normalizePinnedName f.getId) else f
  let mut use ← `(tactic| fail "no named source frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | snapshot_fact $fact | ($use:tactic))
  let mut unfoldAtom ← `(tactic| fail "not a source wrapper")
  for name in #[
    ``Leanux.branch, ``Leanux.branchCmp, ``Leanux.branchCmpExcluded,
    ``Leanux.unsupported, ``Leanux.invariant, ``Leanux.hidden,
    ``Leanux.hiddenU64, ``Leanux.hiddenClock, ``Leanux.hiddenClock64,
    ``Leanux.hiddenJiffies, ``Leanux.hiddenAlloc, ``Leanux.peekHiddenSite,
    ``Leanux.skipCut, ``Leanux.skipCutExactly, ``Leanux.getAmbient,
    ``Leanux.modifyAmbient, ``Leanux.getRouting, ``Leanux.refcountDecAndTest,
    ``Leanux.refcountInc, ``Leanux.refcountIncGuestWide, ``Leanux.refcountIncNotZero,
    ``Leanux.WG.AipNode.bitAt, ``Leanux.WG.choose, ``Leanux.WG.commonBits,
    ``Leanux.WG.prefixMatches, ``Leanux.WG.newTxSkb, ``Leanux.WG.getTxSkb,
    ``Leanux.WG.setTxSkb, ``Leanux.WG.freeTxSkb, ``Leanux.WG.newRxSkb,
    ``Leanux.WG.getRxSkb, ``Leanux.WG.setRxSkb, ``Leanux.WG.freeRxSkb,
    ``Leanux.WG.andM, ``Leanux.WG.orM, ``liftM].reverse do
    let atom := Lean.mkCIdent name
    unfoldAtom ← `(tactic| first | (snapshot_head $atom; unfold $atom) | ($unfoldAtom:tactic))
  let unfoldSource ← if pinned.isEmpty then `(tactic| skip)
    else `(tactic| unfold $pinned:ident*)
  `(tactic|
    (have checkedAmbient {α : Type} (a : AmbientM α) : SameSnapshot (monadLift a : WG.M α) :=
       fun initial => Framing.hoare_liftAmbient a (fun w => snapshot w = initial)
     have checkedAip {α : Type} (a : AipM α) : SameSnapshot (monadLift a : WG.M α) := by
       intro initial
       apply Framing.hoare_liftAip a (fun w => snapshot w = initial)
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have checkedSkb {α : Type} (a : SkbM α) : SameSnapshot (liftSkb a) := by
       intro initial
       apply Framing.hoare_liftSkb a (fun w => snapshot w = initial)
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have checkedIndex {α : Type} (a : IndexM α) : SameSnapshot (monadLift a : WG.M α) := by
       intro initial
       apply Framing.hoare_liftIndex a (fun w => snapshot w = initial)
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have checkedRouting {α : Type} (a : Net.M α) : SameSnapshot (monadLift a : WG.M α) :=
       fun initial => Framing.hoare_liftRouting a (fun w => snapshot w = initial) (fun _ _ hg => hg)
     have checkedGet : SameSnapshot (get : WG.M WGWorld) := by
       apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
       rfl
     have checkedStop {α : Type} (e : Stop) : SameSnapshot (throw e : WG.M α) := by
       apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hr
       cases hr
     have checkedEdit (f : Device → Device) (hf : ∀ d, (f d).keypairs = d.keypairs) :
         SameSnapshot (modifyDev f) :=
       fun initial => modifyDev_snapshot_spec (fun s => s = initial) f hf
     have checkedLoop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameSnapshot (f x b)) : SameSnapshot (forIn xs b f) :=
       fun initial => list_snapshot_spec (fun s => s = initial) xs b f (fun x b => hf x b initial)
     $unfoldSource
     repeat' first
       | snapshot_join_let
       | snapshot_join_use
       | ($use:tactic)
       | ($unfoldAtom:tactic)
       | (snapshot_head liftSkb; exact checkedSkb _)
       | (snapshot_head MonadLiftT.monadLift; first
           | with_reducible exact checkedAmbient _
           | with_reducible exact checkedAip _
           | with_reducible exact checkedSkb _
           | with_reducible exact checkedIndex _
           | with_reducible exact checkedRouting _)
       | (snapshot_head MonadLift.monadLift; first
           | with_reducible exact checkedAmbient _
           | with_reducible exact checkedAip _
           | with_reducible exact checkedSkb _
           | with_reducible exact checkedIndex _
           | with_reducible exact checkedRouting _)
       | (snapshot_head get; exact checkedGet)
       | (snapshot_head MonadStateOf.get; exact checkedGet)
       | (snapshot_head throw; exact checkedStop _)
       | (snapshot_head MonadExceptOf.throw; exact checkedStop _)
       | (snapshot_head modifyDev; apply checkedEdit; intro d; rfl)
       | (snapshot_head ForIn.forIn; first | apply checkedLoop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
       | (snapshot_head StateT.map; apply Framing.SameView.map)
       | contradiction
       | keypairs_intro_forall
       | (snapshot_head Pure.pure; exact snapshot_pure _)
       | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
       | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
       | (snapshot_head modify; refine snapshot_modify (project := id) _ ?_; intro w; exact ⟨rfl, rfl⟩)
       | snapshot_head_reduce
       | snapshot_head_match))

/-- The socket-control mask retains the legacy receive-state view. -/
theorem sameSnapshot_of_sameSocket
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : Framing.SameView
      (fun s => (Framing.socketView (project s)).toWGStoreView) a) :
    Framing.SameView (fun s => snapshot (project s)) a := by
  apply h.of_factor snapshotOfWGStoreView (fun s => snapshot (project s))
  intro s
  simp [snapshot, snapshotOfWGStoreView, Framing.socketView, Framing.socketDevice,
    Framing.wgOwnedView, Framing.wgStoreView, Option.bind_map, Function.comp_def]

theorem sameSnapshot_of_sameConfiguration
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : Framing.SameView
      (fun s => (Framing.configurationView (project s)).toWGStoreView) a) :
    Framing.SameView (fun s => snapshot (project s)) a := by
  apply h.of_factor snapshotOfWGStoreView (fun s => snapshot (project s))
  intro s
  simp [snapshot, snapshotOfWGStoreView, Framing.configurationView,
    Framing.configurationDevice, Framing.wgOwnedView, Framing.wgStoreView,
    Option.bind_map, Function.comp_def]

theorem PrevQueue_dequeue_sameSnapshot {α : Type} (q : PrevQueue α) : SameSnapshot (Leanux.WG.PrevQueue.dequeue (α := α) q) := by
  snapshot_source [Leanux.WG.PrevQueue.dequeue] using []

theorem PrevQueue_dequeue_spec (P : Snapshot → Prop) {α : Type} (q : PrevQueue α) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.PrevQueue.dequeue (α := α) q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (PrevQueue_dequeue_sameSnapshot (α := α) q).wp P

theorem birthdateTest_sameSnapshot (birthday : Int64) (seconds : Nat) : SameSnapshot (Leanux.WG.birthdateTest birthday seconds) :=
  (Framing.birthdateTest_sameWGWorld birthday seconds).factor snapshot

theorem birthdateTest_spec (P : Snapshot → Prop) (birthday : Int64) (seconds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.birthdateTest birthday seconds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (birthdateTest_sameSnapshot birthday seconds).wp P

theorem birthdateHasExpired_sameSnapshot (birthday : Int64) (seconds : Nat) : SameSnapshot (Leanux.WG.birthdateHasExpired birthday seconds) :=
  (Framing.birthdateHasExpired_sameWGWorld birthday seconds).factor snapshot

theorem birthdateHasExpired_spec (P : Snapshot → Prop) (birthday : Int64) (seconds : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.birthdateHasExpired birthday seconds
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (birthdateHasExpired_sameSnapshot birthday seconds).wp P

theorem branchExpired_sameSnapshot (d : Decision) (birthday : Int64) (seconds : Nat) (f : Bool → Bool := id) : SameSnapshot (Leanux.WG.branchExpired d birthday seconds f) :=
  (Framing.branchExpired_sameWGWorld d birthday seconds f).factor snapshot

theorem branchExpired_spec (P : Snapshot → Prop) (d : Decision) (birthday : Int64) (seconds : Nat) (f : Bool → Bool := id) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.branchExpired d birthday seconds f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (branchExpired_sameSnapshot d birthday seconds f).wp P

theorem endpointEq_sameSnapshot (a : Endpoint) (b : Option Endpoint) : SameSnapshot (Leanux.WG.endpointEq a b) := by
  snapshot_source [Leanux.WG.endpointEq] using []

theorem endpointEq_spec (P : Snapshot → Prop) (a : Endpoint) (b : Option Endpoint) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.endpointEq a b
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (endpointEq_sameSnapshot a b).wp P

theorem generatePublic_sameSnapshot (secret : Key) : SameSnapshot (Leanux.WG.generatePublic secret) :=
  (Framing.generatePublic_sameWGWorld secret).factor snapshot

theorem generatePublic_spec (P : Snapshot → Prop) (secret : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.generatePublic secret
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (generatePublic_sameSnapshot secret).wp P

theorem getDev_sameSnapshot  : SameSnapshot (Leanux.WG.getDev ) := by
  snapshot_source [Leanux.WG.getDev] using []

theorem getDev_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getDev
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getDev_sameSnapshot ).wp P

theorem keypairPutNull_sameSnapshot  : SameSnapshot (Leanux.WG.keypairPutNull ) := by
  snapshot_source [Leanux.WG.keypairPutNull] using []

theorem keypairPutNull_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairPutNull
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairPutNull_sameSnapshot ).wp P

theorem mayHaveSlept_sameSnapshot  : SameSnapshot (Leanux.WG.mayHaveSlept ) := by
  snapshot_source [Leanux.WG.mayHaveSlept] using []

theorem mayHaveSlept_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mayHaveSlept
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mayHaveSlept_sameSnapshot ).wp P

theorem raiseLoopbackRx_sameSnapshot  : SameSnapshot (Leanux.WG.raiseLoopbackRx ) := by
  snapshot_source [Leanux.WG.raiseLoopbackRx] using []

theorem raiseLoopbackRx_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.raiseLoopbackRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (raiseLoopbackRx_sameSnapshot ).wp P

theorem setPeer_sameSnapshot (id : PeerId) (p : Peer) : SameSnapshot (Leanux.WG.setPeer id p) := by
  snapshot_source [Leanux.WG.setPeer] using []

theorem setPeer_spec (P : Snapshot → Prop) (id : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeer id p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeer_sameSnapshot id p).wp P

theorem sockFree_sameSnapshot (sock : Option Nat) : SameSnapshot (Leanux.WG.sockFree sock) := by
  exact (Framing.sockFree_sameWGWorld sock).factor snapshot

theorem sockFree_spec (P : Snapshot → Prop) (sock : Option Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sockFree sock
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sockFree_sameSnapshot sock).wp P

theorem swapEndian_sameSnapshot (bits : Nat) : SameSnapshot (Leanux.WG.swapEndian bits) := by
  snapshot_source [Leanux.WG.swapEndian] using []

theorem swapEndian_spec (P : Snapshot → Prop) (bits : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.swapEndian bits
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (swapEndian_sameSnapshot bits).wp P

theorem PrevQueue_peek_sameSnapshot {α : Type} (q : PrevQueue α) : SameSnapshot (Leanux.WG.PrevQueue.peek (α := α) q) := by
  snapshot_source [Leanux.WG.PrevQueue.peek] using [PrevQueue_dequeue_sameSnapshot]

theorem PrevQueue_peek_spec (P : Snapshot → Prop) {α : Type} (q : PrevQueue α) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.PrevQueue.peek (α := α) q
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (PrevQueue_peek_sameSnapshot (α := α) q).wp P

theorem cookiePrecomputeDeviceKeys_sameSnapshot  : SameSnapshot (Leanux.WG.cookiePrecomputeDeviceKeys ) :=
  sameSnapshot_of_sameConfiguration (project := id)
    (Framing.cookiePrecomputeDeviceKeys_sameConfiguration.factor Framing.WGOwnedView.toWGStoreView)

theorem cookiePrecomputeDeviceKeys_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cookiePrecomputeDeviceKeys
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookiePrecomputeDeviceKeys_sameSnapshot ).wp P

theorem getKeypair_sameSnapshot (id : KeypairId) : SameSnapshot (Leanux.WG.getKeypair id) := by
  snapshot_source [Leanux.WG.getKeypair] using [getDev_sameSnapshot]

theorem getKeypair_spec (P : Snapshot → Prop) (id : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getKeypair id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getKeypair_sameSnapshot id).wp P

theorem getPeer_sameSnapshot (id : PeerId) : SameSnapshot (Leanux.WG.getPeer id) := by
  snapshot_source [Leanux.WG.getPeer] using [getDev_sameSnapshot]

theorem getPeer_spec (P : Snapshot → Prop) (id : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.getPeer id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (getPeer_sameSnapshot id).wp P

/-- The embedded word is read through its owner; only successful states are
framed here. Lifetime observers separately record the resolved owner access. -/
theorem ownerPeerWord_sameSnapshot (owner : IndexOwner) :
    SameSnapshot owner.peerWord := by
  cases owner <;> snapshot_source [IndexOwner.peerWord] using [getPeer_sameSnapshot, getKeypair_sameSnapshot]

theorem ownerPeerWord_spec (P : Snapshot → Prop) (owner : IndexOwner) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ owner.peerWord
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ownerPeerWord_sameSnapshot owner).wp P

/-- The setter rereads its current owner. Updating its peer word retains the
actual keypair counter cell; no whole-store mask is introduced. -/
theorem ownerSetPeerWord_sameSnapshot (owner : IndexOwner) (peer : Option PeerId) :
    SameSnapshot (owner.setPeerWord peer) := by
  cases owner with
  | handshake pid =>
    snapshot_source [IndexOwner.setPeerWord] using [getPeer_sameSnapshot, setPeer_sameSnapshot]
  | keypair kp =>
    apply sameSnapshot_of_wp
    intro initial
    unfold IndexOwner.setPeerWord
    refine Std.Do.Triple.bind _ _ (getKeypair_live_spec (fun s => s = initial) kp) ?_
    intro key
    exact setKeypair_live_spec (fun s => s = initial) kp {key with peer}

theorem ownerSetPeerWord_spec (P : Snapshot → Prop) (owner : IndexOwner)
    (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ owner.setPeerWord peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ownerSetPeerWord_sameSnapshot owner peer).wp P

theorem ownerPeerDeref_sameSnapshot (owner : IndexOwner) :
    SameSnapshot owner.peerDeref := by
  snapshot_source [IndexOwner.peerDeref] using [ownerPeerWord_sameSnapshot]

theorem ownerPeerDeref_spec (P : Snapshot → Prop) (owner : IndexOwner) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ owner.peerDeref
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ownerPeerDeref_sameSnapshot owner).wp P

theorem listDel_sameSnapshot (id : NodeId) : SameSnapshot (Leanux.WG.listDel id) := by
  snapshot_source [Leanux.WG.listDel] using [getDev_sameSnapshot, setPeer_sameSnapshot]

theorem listDel_spec (P : Snapshot → Prop) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.listDel id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listDel_sameSnapshot id).wp P

theorem loopbackSoftirq_sameSnapshot  : SameSnapshot (Leanux.WG.loopbackSoftirq ) := by
  snapshot_source [Leanux.WG.loopbackSoftirq] using [getDev_sameSnapshot]

theorem loopbackSoftirq_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.loopbackSoftirq
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (loopbackSoftirq_sameSnapshot ).wp P

theorem readNode_sameSnapshot (n : AipNode) : SameSnapshot (Leanux.WG.readNode n) := by
  snapshot_source [Leanux.WG.readNode] using [swapEndian_sameSnapshot]

theorem readNode_spec (P : Snapshot → Prop) (n : AipNode) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.readNode n
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (readNode_sameSnapshot n).wp P

theorem socketPort_sameSnapshot (family : Nat) : SameSnapshot (Leanux.WG.socketPort family) := by
  snapshot_source [Leanux.WG.socketPort] using [getDev_sameSnapshot]

theorem socketPort_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketPort family
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketPort_sameSnapshot family).wp P

theorem socketReinit_sameSnapshot (new4 new6 : Option Nat) : SameSnapshot (Leanux.WG.socketReinit new4 new6) := by
  exact sameSnapshot_of_sameSocket (project := id)
    ((Framing.socketReinit_sameSocket new4 new6).factor Framing.WGOwnedView.toWGStoreView)

theorem socketReinit_spec (P : Snapshot → Prop) (new4 new6 : Option Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketReinit new4 new6
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketReinit_sameSnapshot new4 new6).wp P

theorem armTimer_sameSnapshot (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) : SameSnapshot (Leanux.WG.armTimer pid t delay jc) := by
  have wheel (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameSnapshot (Leanux.WG.placeOnWheel pid t expires clk unit) := by
    snapshot_source [Leanux.WG.placeOnWheel] using [getPeer_sameSnapshot, setPeer_sameSnapshot]
  have ambient {α : Type} (a : AmbientM α) : SameSnapshot (monadLift a : WG.M α) :=
    fun initial => Framing.hoare_liftAmbient a (fun w => snapshot w = initial)
  have read : SameSnapshot (get : WG.M WGWorld) := by snapshot_source [] using []
  have stopped {α : Type} (e : Stop) : SameSnapshot (throw e : WG.M α) := by
    snapshot_source [] using []
  unfold Leanux.WG.armTimer
  simp (config := { zeta := false }) only [Leanux.getAmbient, Leanux.hidden, Leanux.invariant, Leanux.unsupported]
  repeat' first
    | snapshot_join_let
    | snapshot_join_use
    | (snapshot_head Leanux.WG.placeOnWheel; exact wheel _ _ _ _ _)
    | (snapshot_head Leanux.WG.getDev; exact getDev_sameSnapshot)
    | (snapshot_head Leanux.WG.getPeer; exact getPeer_sameSnapshot _)
    | (snapshot_head MonadLiftT.monadLift; exact ambient _)
    | (snapshot_head MonadLift.monadLift; exact ambient _)
    | (snapshot_head get; exact read)
    | (snapshot_head MonadStateOf.get; exact read)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | snapshot_head_reduce
    | snapshot_head_match

theorem armTimer_spec (P : Snapshot → Prop) (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.armTimer pid t delay jc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (armTimer_sameSnapshot pid t delay jc).wp P

theorem delTimer_sameSnapshot (pid : PeerId) (t : PeerTimer) : SameSnapshot (Leanux.WG.delTimer pid t) := by
  snapshot_source [Leanux.WG.delTimer] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem delTimer_spec (P : Snapshot → Prop) (pid : PeerId) (t : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.delTimer pid t
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (delTimer_sameSnapshot pid t).wp P

theorem dstCacheGet_sameSnapshot (pid : PeerId) (gen : Nat) : SameSnapshot (Leanux.WG.dstCacheGet pid gen) := by
  snapshot_source [Leanux.WG.dstCacheGet] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem dstCacheGet_spec (P : Snapshot → Prop) (pid : PeerId) (gen : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheGet pid gen
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheGet_sameSnapshot pid gen).wp P

theorem dstCacheReset_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.dstCacheReset pid) := by
  snapshot_source [Leanux.WG.dstCacheReset] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem dstCacheReset_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheReset pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheReset_sameSnapshot pid).wp P

theorem dstCacheSet_sameSnapshot (pid : PeerId) (src gen dev : Nat) : SameSnapshot (Leanux.WG.dstCacheSet pid src gen dev) := by
  snapshot_source [Leanux.WG.dstCacheSet] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem dstCacheSet_spec (P : Snapshot → Prop) (pid : PeerId) (src gen dev : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheSet pid src gen dev
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheSet_sameSnapshot pid src gen dev).wp P

theorem handshakeZero_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeZero pid) := by
  snapshot_source [Leanux.WG.handshakeZero] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem handshakeZero_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeZero pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeZero_sameSnapshot pid).wp P

theorem listAddTail_sameSnapshot (peer : PeerId) (id : NodeId) : SameSnapshot (Leanux.WG.listAddTail peer id) := by
  snapshot_source [Leanux.WG.listAddTail] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem listAddTail_spec (P : Snapshot → Prop) (peer : PeerId) (id : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.listAddTail peer id
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (listAddTail_sameSnapshot peer id).wp P

theorem loopbackSend_sameSnapshot (sites : List HiddenSite) (raised : Bool) : SameSnapshot (Leanux.WG.loopbackSend sites raised) := by
  snapshot_source [Leanux.WG.loopbackSend] using [loopbackSoftirq_sameSnapshot, raiseLoopbackRx_sameSnapshot]

theorem loopbackSend_spec (P : Snapshot → Prop) (sites : List HiddenSite) (raised : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.loopbackSend sites raised
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (loopbackSend_sameSnapshot sites raised).wp P

theorem requireNotPending_sameSnapshot (pid : PeerId) (what : String) : SameSnapshot (Leanux.WG.requireNotPending pid what) := by
  snapshot_source [Leanux.WG.requireNotPending] using [getPeer_sameSnapshot]

theorem requireNotPending_spec (P : Snapshot → Prop) (pid : PeerId) (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.requireNotPending pid what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (requireNotPending_sameSnapshot pid what).wp P

theorem resetLastSentHandshake_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.resetLastSentHandshake pid) := by
  snapshot_source [Leanux.WG.resetLastSentHandshake] using [getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem resetLastSentHandshake_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.resetLastSentHandshake pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (resetLastSentHandshake_sameSnapshot pid).wp P

theorem rootRemovePeerLists_sameSnapshot (root : NodeId) : SameSnapshot (Leanux.WG.rootRemovePeerLists root) := by
  snapshot_source [Leanux.WG.rootRemovePeerLists] using [getDev_sameSnapshot, getPeer_sameSnapshot, listDel_sameSnapshot]

theorem rootRemovePeerLists_spec (P : Snapshot → Prop) (root : NodeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.rootRemovePeerLists root
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (rootRemovePeerLists_sameSnapshot root).wp P

theorem socketInit_sameSnapshot (port : Nat) : SameSnapshot (Leanux.WG.socketInit port) := by
  exact sameSnapshot_of_sameSocket (project := id)
    ((Framing.socketInit_sameSocket port).factor Framing.WGOwnedView.toWGStoreView)

theorem socketInit_spec (P : Snapshot → Prop) (port : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.socketInit port
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketInit_sameSnapshot port).wp P

theorem dstCacheResetNow_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.dstCacheResetNow pid) := by
  snapshot_source [Leanux.WG.dstCacheResetNow] using [dstCacheReset_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem dstCacheResetNow_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.dstCacheResetNow pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (dstCacheResetNow_sameSnapshot pid).wp P

theorem free_sameSnapshot  : SameSnapshot (Leanux.WG.free ) := by
  snapshot_source [Leanux.WG.free] using [getDev_sameSnapshot, rootRemovePeerLists_sameSnapshot]

theorem free_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.free
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (free_sameSnapshot ).wp P

theorem peerGet_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.peerGet pid) := by
  snapshot_source [Leanux.WG.peerGet] using [getPeer_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem peerGet_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerGet pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerGet_sameSnapshot pid).wp P

theorem peerGetMaybeZero_sameSnapshot (peer : Option PeerId) : SameSnapshot (Leanux.WG.peerGetMaybeZero peer) := by
  snapshot_source [Leanux.WG.peerGetMaybeZero] using [getPeer_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem peerGetMaybeZero_spec (P : Snapshot → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerGetMaybeZero peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerGetMaybeZero_sameSnapshot peer).wp P

theorem peerPut_sameSnapshot (peer : Option PeerId) : SameSnapshot (Leanux.WG.peerPut peer) := by
  snapshot_source [Leanux.WG.peerPut, Leanux.retirePeerUnits] using [getPeer_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem peerPut_spec (P : Snapshot → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerPut peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerPut_sameSnapshot peer).wp P

theorem precomputeStaticStatic_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.precomputeStaticStatic pid) := by
  snapshot_source [Leanux.WG.precomputeStaticStatic] using [getDev_sameSnapshot, getPeer_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem precomputeStaticStatic_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.precomputeStaticStatic pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (precomputeStaticStatic_sameSnapshot pid).wp P

theorem removeByPeer_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.removeByPeer pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameSnapshot (monadLift a : WG.M α) :=
    fun initial => Framing.hoare_liftAmbient a (fun w => snapshot w = initial)
  have aip {α : Type} (a : AipM α) : SameSnapshot (monadLift a : WG.M α) := by
    intro initial
    apply Framing.hoare_liftAip a (fun w => snapshot w = initial)
    intro g d store hg hd
    simpa [snapshot, hd] using hg
  have edit (f : Device → Device) (hf : ∀ d, (f d).keypairs = d.keypairs) :
      SameSnapshot (modifyDev f) :=
    fun initial => modifyDev_snapshot_spec (fun s => s = initial) f hf
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, SameSnapshot (f x b)) : SameSnapshot (forIn xs b f) :=
    fun initial => list_snapshot_spec (fun s => s = initial) xs b f (fun x b => hf x b initial)
  have stopped {α : Type} (e : Stop) : SameSnapshot (throw e : WG.M α) := by
    snapshot_source [] using []
  unfold Leanux.WG.removeByPeer
  simp (config := { zeta := false }) only [Leanux.branch, Leanux.invariant, Leanux.WG.AipNode.bitAt, liftM]
  repeat' first
    | snapshot_join_let
    | snapshot_join_use
    | (snapshot_head Leanux.WG.getPeer; exact getPeer_sameSnapshot _)
    | (snapshot_head Leanux.WG.listDel; exact listDel_sameSnapshot _)
    | (snapshot_head MonadLiftT.monadLift; first | with_reducible exact ambient _ | with_reducible exact aip _)
    | (snapshot_head MonadLift.monadLift; first | with_reducible exact ambient _ | with_reducible exact aip _)
    | (snapshot_head modifyDev; exact edit _ (fun _ => rfl))
    | (snapshot_head ForIn.forIn; apply loop)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | snapshot_head_reduce
    | snapshot_head_match

theorem removeByPeer_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.removeByPeer pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (removeByPeer_sameSnapshot pid).wp P

theorem setPeerEndpoint_sameSnapshot (pid : PeerId) (e : Endpoint) : SameSnapshot (Leanux.WG.setPeerEndpoint pid e) := by
  snapshot_source [Leanux.WG.setPeerEndpoint] using [dstCacheReset_sameSnapshot, endpointEq_sameSnapshot, getPeer_sameSnapshot, requireNotPending_sameSnapshot, setPeer_sameSnapshot]

theorem setPeerEndpoint_spec (P : Snapshot → Prop) (pid : PeerId) (e : Endpoint) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeerEndpoint pid e
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeerEndpoint_sameSnapshot pid e).wp P

theorem setStaticIdentityPrivateKey_sameSnapshot (privateKey : Key) : SameSnapshot (Leanux.WG.setStaticIdentityPrivateKey privateKey) :=
  sameSnapshot_of_sameConfiguration (project := id)
    ((Framing.setStaticIdentityPrivateKey_sameConfiguration privateKey).factor Framing.WGOwnedView.toWGStoreView)

theorem setStaticIdentityPrivateKey_spec (P : Snapshot → Prop) (privateKey : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setStaticIdentityPrivateKey privateKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setStaticIdentityPrivateKey_sameSnapshot privateKey).wp P

theorem tunnelXmit_sameSnapshot (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : SameSnapshot ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  snapshot_source [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit] using [loopbackSend_sameSnapshot, socketPort_sameSnapshot]

theorem tunnelXmit_spec (P : Snapshot → Prop) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (tunnelXmit_sameSnapshot e bytes ds r exactRx).wp P

theorem clearPeerEndpointSrc_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.clearPeerEndpointSrc pid) := by
  snapshot_source [Leanux.WG.clearPeerEndpointSrc] using [dstCacheResetNow_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot]

theorem clearPeerEndpointSrc_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (clearPeerEndpointSrc_sameSnapshot pid).wp P

theorem handshakeInit_sameSnapshot (pid : PeerId) (presharedKey : Option Key) : SameSnapshot (Leanux.WG.handshakeInit pid presharedKey) := by
  snapshot_source [Leanux.WG.handshakeInit] using [ownerSetPeerWord_sameSnapshot, getPeer_sameSnapshot, precomputeStaticStatic_sameSnapshot, setPeer_sameSnapshot]

theorem handshakeInit_spec (P : Snapshot → Prop) (pid : PeerId) (presharedKey : Option Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeInit pid presharedKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeInit_sameSnapshot pid presharedKey).wp P

theorem indexLookup_sameSnapshot (kinds : List IndexKind) (index : Nat) : SameSnapshot (Leanux.WG.indexLookup kinds index) := by
  snapshot_source [Leanux.WG.indexLookup] using [ownerPeerWord_sameSnapshot, ownerSetPeerWord_sameSnapshot, peerGetMaybeZero_sameSnapshot]

theorem indexLookup_spec (P : Snapshot → Prop) (kinds : List IndexKind) (index : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.indexLookup kinds index
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (indexLookup_sameSnapshot kinds index).wp P

theorem peerMakeDead_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.peerMakeDead pid) := by
  snapshot_source [Leanux.WG.peerMakeDead] using [getDev_sameSnapshot, getPeer_sameSnapshot, removeByPeer_sameSnapshot, setPeer_sameSnapshot]

theorem peerMakeDead_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerMakeDead pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerMakeDead_sameSnapshot pid).wp P

theorem pubkeyLookup_sameSnapshot (key : Key) : SameSnapshot (Leanux.WG.pubkeyLookup key) := by
  snapshot_source [Leanux.WG.pubkeyLookup] using [getDev_sameSnapshot, peerGetMaybeZero_sameSnapshot]

theorem pubkeyLookup_spec (P : Snapshot → Prop) (key : Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.pubkeyLookup key
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pubkeyLookup_sameSnapshot key).wp P

theorem send4_sameSnapshot (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : SameSnapshot (Leanux.WG.send4 e cache bytes ds exactRx) := by
  have ambient {α : Type} (a : AmbientM α) : SameSnapshot (monadLift a : WG.M α) :=
    fun initial => Framing.hoare_liftAmbient a (fun w => snapshot w = initial)
  have routing {α : Type} (a : Net.M α) : SameSnapshot (monadLift a : WG.M α) :=
    fun initial => Framing.hoare_liftRouting a (fun w => snapshot w = initial) (fun _ _ hg => hg)
  have read : SameSnapshot (get : WG.M WGWorld) := by snapshot_source [] using []
  have stopped {α : Type} (e : Stop) : SameSnapshot (throw e : WG.M α) := by
    snapshot_source [] using []
  unfold Leanux.WG.send4
  simp (config := { zeta := false }) only [Leanux.branch, Leanux.invariant, Leanux.getRouting, liftM]
  repeat' first
    | snapshot_join_let
    | snapshot_join_use
    | (snapshot_head Leanux.WG.getDev; exact getDev_sameSnapshot)
    | (snapshot_head Leanux.WG.getPeer; exact getPeer_sameSnapshot _)
    | (snapshot_head Leanux.WG.setPeer; exact setPeer_sameSnapshot _ _)
    | (snapshot_head Leanux.WG.dstCacheGet; exact dstCacheGet_sameSnapshot _ _)
    | (snapshot_head Leanux.WG.dstCacheReset; exact dstCacheReset_sameSnapshot _)
    | (snapshot_head Leanux.WG.dstCacheSet; exact dstCacheSet_sameSnapshot _ _ _ _)
    | (snapshot_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnelXmit_sameSnapshot _ _ _ _ _)
    | (snapshot_head MonadLiftT.monadLift; first | with_reducible exact ambient _ | with_reducible exact routing _)
    | (snapshot_head MonadLift.monadLift; first | with_reducible exact ambient _ | with_reducible exact routing _)
    | (snapshot_head get; exact read)
    | (snapshot_head MonadStateOf.get; exact read)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | snapshot_head_reduce
    | snapshot_head_match

theorem send4_spec (P : Snapshot → Prop) (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.send4 e cache bytes ds exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (send4_sameSnapshot e cache bytes ds exactRx).wp P

theorem send6_sameSnapshot (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : SameSnapshot (Leanux.WG.send6 e cache bytes ds exactRx) := by
  snapshot_source [Leanux.WG.send6] using [dstCacheGet_sameSnapshot, dstCacheReset_sameSnapshot, dstCacheSet_sameSnapshot, getDev_sameSnapshot, getPeer_sameSnapshot, setPeer_sameSnapshot, tunnelXmit_sameSnapshot]

theorem send6_spec (P : Snapshot → Prop) (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.send6 e cache bytes ds exactRx
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (send6_sameSnapshot e cache bytes ds exactRx).wp P

theorem add_sameSnapshot (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : SameSnapshot (Leanux.WG.add root bits key cidr peer) := by
  have ambient {α : Type} (a : AmbientM α) : SameSnapshot (monadLift a : WG.M α) :=
    fun initial => Framing.hoare_liftAmbient a (fun w => snapshot w = initial)
  have aip {α : Type} (a : AipM α) : SameSnapshot (monadLift a : WG.M α) := by
    intro initial
    apply Framing.hoare_liftAip a (fun w => snapshot w = initial)
    intro g d store hg hd
    simpa [snapshot, hd] using hg
  have stopped {α : Type} (e : Stop) : SameSnapshot (throw e : WG.M α) := by
    snapshot_source [] using []
  unfold Leanux.WG.add
  simp (config := { zeta := false }) only [Leanux.branch, Leanux.branchCmp, Leanux.invariant,
    Leanux.WG.choose, Leanux.WG.AipNode.bitAt, Leanux.WG.commonBits, liftM]
  repeat' first
    | snapshot_join_let
    | snapshot_join_use
    | (snapshot_head Leanux.WG.listAddTail; exact listAddTail_sameSnapshot _ _)
    | (snapshot_head Leanux.WG.listDel; exact listDel_sameSnapshot _)
    | (snapshot_head MonadLiftT.monadLift; first | with_reducible exact ambient _ | with_reducible exact aip _)
    | (snapshot_head MonadLift.monadLift; first | with_reducible exact ambient _ | with_reducible exact aip _)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | snapshot_head_reduce
    | snapshot_head_match

theorem add_spec (P : Snapshot → Prop) (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.add root bits key cidr peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (add_sameSnapshot root bits key cidr peer).wp P

theorem peerCreate_sameSnapshot (publicKey : Key) (presharedKey : Option Key) : SameSnapshot (Leanux.WG.peerCreate publicKey presharedKey) := by
  snapshot_source [Leanux.WG.peerCreate] using [dstCacheReset_sameSnapshot, getDev_sameSnapshot, handshakeInit_sameSnapshot, resetLastSentHandshake_sameSnapshot, setPeer_sameSnapshot]

theorem peerCreate_spec (P : Snapshot → Prop) (publicKey : Key) (presharedKey : Option Key) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.peerCreate publicKey presharedKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peerCreate_sameSnapshot publicKey presharedKey).wp P

theorem insert_sameSnapshot (family : Nat) (addr cidr : Nat) (peer : PeerId) : SameSnapshot (Leanux.WG.insert family addr cidr peer) := by
  snapshot_source [Leanux.WG.insert] using [add_sameSnapshot]

theorem insert_spec (P : Snapshot → Prop) (family : Nat) (addr cidr : Nat) (peer : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.insert family addr cidr peer
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (insert_sameSnapshot family addr cidr peer).wp P

end Leanux.Proofs.WG.Keypairs.WGFrames
