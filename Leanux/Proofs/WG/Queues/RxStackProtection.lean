import Leanux.Proofs.WG.Queues.RxKeyProtection

/-! Actual stack replies preserve a supplied RX carrier ledger. The destination
lookup supplies its own positive reference loan; repayment retains any typed
TX/send-work handoff made by the concrete staged-send call. Normal error codes
are included. No stack success, peer residency or failed World is assumed. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option pp.structureInstances false

theorem Handoff.with_loans (h : Handoff w v before after d) (loans : Reservations) :
    Handoff w v (before++loans) (after++loans) d := by
  refine ⟨h.base,h.rx,h.tx,h.send,?_⟩
  intro o
  have hc := h.count o
  simp only [List.count_append]
  omega

/-- The actual positive pre-borrow balance prevents final repayment from
retiring its owner, even when staging has made nonempty durable handoffs. -/
theorem repay_handoff_delta (h : Handoff w u [] [o] delta) (pos : 0<balance w o)
    (hr : ((peerPut (some o.slot)).run u).run ambient=.ok (((),v),ambient')) : Handoff w v [] [] delta := by
  have hc := h.count o
  simp only [List.count_cons_self,List.count_nil,Nat.add_zero] at hc
  have hu : 1<balance u o := by omega
  cases hp : resident u o with
  | none => simp [balance,hp] at hu
  | some p =>
    obtain ⟨d,hd,he,hs,ht⟩ := resident_fields hp
    have count : 1<p.refcount := by simpa [balance,hp] using hu
    have ho : o=⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
    have paid := peerPut_handoff hd hs count ambient ambient' hr
    rw [←ho] at paid
    simpa [HandoffDelta.append] using h.trans paid

theorem borrowed_keyView (h : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    keyView v=keyView w := by
  cases result with
  | none =>
    have hd : v.dev = w.dev := congrArg WGStoreView.dev h
    unfold keyView keyWords currentCells
    rw [hd]
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv⟩ := h
    apply keyView_affiliation
    have hvd := congrArg WGStoreView.dev hv
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at hvd
    change w.dev = some d at hd
    simp only [Affiliation.view,hvd,hd,Option.map_some]
    exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount:=p.refcount+1} hp rfl)

theorem lookupDst_keyView (family addr : Nat) : SameView keyView (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_keyView ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient result v ambient' rfl hr)

private theorem xmitTrim_control (pid : PeerId) :
    SameView controlView (Lifetimes.xmitTrim pid) := by
  have dropped : SameView controlView (modifyDev fun d => {d with txDropped := d.txDropped+1}) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
    unfold controlView protectView peerView rxView handoffTxView sendView currentKey keyWords
    simp [Option.map_map,Option.bind_map,Function.comp_def]
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (Lifetimes.xmitTrim pid) := by
    unfold Lifetimes.xmitTrim
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    material_lower
    repeat' first
      | (index_material_head ForIn.forIn
         apply list_view_spec controlView (fun obs => obs = controlView initial)
         intro idx acc)
      | (index_material_head modifyDev; exact dropped.wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
    all_goals simp_all only [controlCell,protectCell]
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem xmitTrim_keyView (pid : PeerId) : SameView keyView (Lifetimes.xmitTrim pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  exact control_keyView ((ProjectedAction.iff_run_ambient _ _ _).mp
    (xmitTrim_control pid) w ambient x v ambient' hr)

theorem xmitSplice_keyView (pid : PeerId) (packets : List WG.Packet) : SameView keyView (Lifetimes.xmitSplice pid packets) := by
  simp only [Lifetimes.xmitSplice,getPeer_twice]
  exact modifyPeer_keyView pid (fun p => {p with staged:=p.staged++packets}) (fun _ => rfl)

elab "rx_stack_as_hoare " P:term : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``Triple do Lean.throwError "not a Triple"
  Lean.Elab.Tactic.evalTactic (← `(tactic| change Hoare _ $P (fun _ => $P)))

macro "rx_stack_basic " P:term : tactic => `(tactic|
  first
    | unfold Preserves
    | rx_stack_as_hoare $P
    | material_join
    | material_join_use
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id $P; intro idx acc)
    | (index_material_head Functor.discard; apply discard_view_spec id $P)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction)

theorem wgXmit_keyEffect (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    KeyEffects allowed (wgXmit family addr packets mtu) := by
  apply keyEffects_of_wp (project := id); intro initial
  let P := KeyEffect allowed initial
  change Hoare _ P (fun _ => P)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors+1}) :=
    KeyEffects.wp (project := id) (keyEffects_view (project := id)
      (modifyDev_keyView (fun d => {d with txErrors := d.txErrors+1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))) initial
  have getter (pid : PeerId) : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_effect allowed initial pid) (fun _ h => h) (fun _ _ h => h.1)
  have device : Preserves P getDev :=
    KeyEffects.wp (project := id) (keyEffects_view (project := id)
      (keyView_kernel (project := id) Lifetimes.getDev_sameWGStore)) initial
  rw [Lifetimes.wgXmitSource_eq]
  unfold Lifetimes.wgXmitSource WG.andM skipCutSites envOk
  material_lower
  repeat' first
    | (index_material_head lookupDst
       exact KeyEffects.wp (project := id) (keyEffects_view (project := id) (lookupDst_keyView _ _)) initial)
    | (index_material_head Lifetimes.xmitTrim
       exact KeyEffects.wp (project := id) (keyEffects_view (project := id) (xmitTrim_keyView _)) initial)
    | (index_material_head Lifetimes.xmitSplice
       exact KeyEffects.wp (project := id) (keyEffects_view (project := id) (xmitSplice_keyView _ _)) initial)
    | (index_material_head sendStagedPackets; exact KeyEffects.wp (project := id) (staged_send_keyEffect _) initial)
    | (index_material_head peerPut; exact KeyEffects.wp (project := id) (peerPut_keyEffect _) initial)
    | (index_material_head loopbackSend
       exact KeyEffects.wp (project := id) (keyEffects_view (project := id)
         (keyView_kernel (project := id) (loopbackSend_kernel _ _))) initial)
    | (index_material_head modifyDev; exact errors)
    | (index_material_head getPeer; exact getter _)
    | (index_material_head getDev; exact device)
    | rx_stack_basic P

def replyView (w : WGWorld) := (protectView w,keyView w)

theorem reply_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => replyView (project w)) a :=
  (protect_kernel ha).product (keyView_kernel ha)

theorem reply_views {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (hp : SameView (fun w => protectView (project w)) a)
    (hk : SameView (fun w => keyView (project w)) a) :
    SameView (fun w => replyView (project w)) a := hp.product hk

theorem currents_view (h : keyView v=keyView w) (hc : CurrentsCompatible w) : CurrentsCompatible v :=
  (keyEffect_of_view (allowed:=NoPromotion) h).currentsCompatible hc (fun _ _ h => False.elim h)

/-- Outstanding source-attributed destination loan. `none` has no loan; the
positive source balance is retained through the exact same accumulated delta. -/
def XmitPending (initial : WGWorld) (peer : Option PeerId) (w : WGWorld) : Prop :=
  CurrentsCompatible w ∧ match peer with
  | none => Transfer initial w
  | some pid => ∃o, o.slot=pid ∧ 0<balance initial o ∧ ∃delta,Handoff initial w [] [o] delta
def XmitClosed (initial w : WGWorld) : Prop := Transfer initial w ∧ CurrentsCompatible w

theorem xmitPending_view (h : XmitPending initial peer w) (he : replyView v=replyView w) : XmitPending initial peer v := by
  refine ⟨currents_view (congrArg Prod.snd he) h.1,?_⟩
  cases peer with
  | none => exact h.2.after_view (congrArg Prod.fst he)
  | some pid =>
    obtain ⟨o,ho,pos,d,hd⟩ := h.2
    exact ⟨o,ho,pos,d,hd.after_view (congrArg Prod.fst he)⟩

theorem xmitClosed_view (h : XmitClosed initial w) (he : replyView v=replyView w) : XmitClosed initial v :=
  ⟨h.1.after_view (congrArg Prod.fst he),currents_view (congrArg Prod.snd he) h.2⟩

theorem pending_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => replyView (project w)) a) (initial : WGWorld) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜XmitPending initial peer (project w)⌝⦄ := by
  apply hoare_consequence (ha.wp (fun obs => ∃ w, XmitPending initial peer w ∧ obs=replyView w))
  · intro w hi; exact ⟨project w,hi,rfl⟩
  · intro x v hi
    obtain ⟨w,h,he⟩ := hi
    exact xmitPending_view h he

theorem closed_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => replyView (project w)) a) (initial : WGWorld) :
    ⦃fun w => ⌜XmitClosed initial (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜XmitClosed initial (project w)⌝⦄ := by
  apply hoare_consequence (ha.wp (fun obs => ∃ w, XmitClosed initial w ∧ obs=replyView w))
  · intro w hi; exact ⟨project w,hi,rfl⟩
  · intro x v hi
    obtain ⟨w,h,he⟩ := hi
    exact xmitClosed_view h he

theorem pending_repay (initial : WGWorld) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer w⌝⦄ peerPut peer
    ⦃⇓? _ w => ⌜XmitClosed initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases x
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (peerPut_keyEffect (allowed:=NoPromotion) peer) w ambient () v ambient' hr
  refine ⟨?_,effect.currentsCompatible hi.1 (fun _ _ h => False.elim h)⟩
  cases peer with
  | none =>
    have hn : SameView protectView (peerPut none) := by
      intro s
      unfold peerPut
      material_lower
      repeat' rx_stack_basic (fun w => protectView w=s)
    exact hi.2.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp hn w ambient () v ambient' hr)
  | some pid =>
    obtain ⟨o,ho,pos,d,hd⟩ := hi.2
    exact ⟨d,repay_handoff_delta hd pos (by simpa [ho] using hr)⟩

theorem pending_stage (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜XmitPending initial (some pid) w⌝⦄ sendStagedPackets pid
    ⦃⇓? _ w => ⌜XmitPending initial (some pid) w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases x
  obtain ⟨o,ho,pos,d,hd⟩ := hi.2
  obtain ⟨new,hn⟩ := staged_send_handoff pid (hi.1 pid) ambient ambient' hr
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (staged_send_keyEffect (allowed:=NoPromotion) pid) w ambient () v ambient' hr
  refine ⟨effect.currentsCompatible hi.1 (fun _ _ h => False.elim h),o,ho,pos,d.append new,?_⟩
  exact hd.trans (by simpa using hn.with_loans [o])

theorem modifyDev_reply (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers)
    (hk : ∀d,(f d).keypairs=d.keypairs) (hr : ∀d,(f d).rxSkbs=d.rxSkbs)
    (hs : ∀d,(f d).sendWorkQueue=d.sendWorkQueue) : SameView replyView (modifyDev f) :=
  reply_views (modifyDev_protect f he hp hr hs) (modifyDev_keyView f he hp hk)

theorem xmitTrim_protect (pid : PeerId) : SameView protectView (Lifetimes.xmitTrim pid) :=
  control_protect (project := id) (xmitTrim_control pid)

theorem xmitSplice_protect (pid : PeerId) (ps : List WG.Packet) : SameView protectView (Lifetimes.xmitSplice pid ps) := by
  simp only [Lifetimes.xmitSplice,getPeer_twice]
  exact modifyPeer_protect pid (fun p => {p with staged:=p.staged++ps}) (fun _ => rfl)

theorem txHeaders_kernel (family addr : Nat) (ps : List WG.Packet) :
    SameWGStore (Packets.txHeaders family addr ps) := by
  intro s
  unfold Packets.txHeaders
  material_lower
  repeat' rx_stack_basic (fun w => wgStoreView w=s)

theorem txWalk_kernel (ps : List WG.Packet) (mtu : Nat) (acc : List WG.Packet) :
    SameWGStore (Packets.txWalk ps mtu acc) := by
  intro s
  unfold Packets.txWalk
  material_lower
  repeat' rx_stack_basic (fun w => wgStoreView w=s)

theorem txCheck_reply (family addr : Nat) (ps : List WG.Packet) (mtu : Nat) :
    SameView replyView (Packets.txCheck family addr ps mtu) := by
  intro s
  have headers := (reply_kernel (project := id) (txHeaders_kernel family addr ps)).wp (fun t => t=s)
  have errors := (modifyDev_reply (fun d => {d with txErrors:=d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  unfold Packets.txCheck WG.andM
  material_lower
  repeat' first
    | (index_material_head Packets.txHeaders; exact headers)
    | (index_material_head modifyDev; exact errors)
    | rx_stack_basic (fun w => replyView w=s)

theorem txError_reply (family : Nat) (first : WG.Packet) (ret : Int) :
    SameView replyView (Packets.txError family first ret) := by
  intro s
  have loop := fun sites raised => (reply_kernel (project := id) (loopbackSend_kernel sites raised)).wp (fun t => t=s)
  have errors := (modifyDev_reply (fun d => {d with txErrors:=d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  unfold Packets.txError skipCutSites
  material_lower
  repeat' first
    | (index_material_head loopbackSend; exact loop _ _)
    | (index_material_head modifyDev; exact errors)
    | rx_stack_basic (fun w => replyView w=s)

theorem lookup_pending (family addr : Nat) (hc : CurrentsCompatible w)
    (hr : ((lookupDst family addr).run w).run ambient=.ok ((peer,v),ambient')) :
    XmitPending w peer v := by
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient peer v ambient' rfl hr
  refine ⟨currents_view (borrowed_keyView hb) hc,?_⟩
  cases peer with
  | none =>
    have hd : v.dev=w.dev := congrArg WGStoreView.dev hb
    exact (Transfer.refl w).after_view (by
      unfold protectView peerView rxView handoffTxView sendView
      rw [hd])
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv⟩ := hb
    change w.dev=some d at hd
    have hvd := congrArg WGStoreView.dev hv
    change v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at hvd
    refine ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,by simp [balance,resident,hd,hp,pos],{},?_⟩
    apply (acquire_handoff hd hp).after_view
    unfold protectView peerView rxView handoffTxView sendView
    simp [creditWorld,hvd]

def SelectedXmit (initial : WGWorld) (result : Except Int (PeerId × List WG.Packet)) (w : WGWorld) : Prop :=
  match result with
  | .error _ => XmitClosed initial w
  | .ok (pid,_) => XmitPending initial (some pid) w

elab "rx_stack_bind_head " name:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let args := t.getAppArgs
  unless t.isAppOf ``Hoare && args.size ≥ 3 do Lean.throwError "not a Hoare contract"
  let a := args[args.size-3]!.consumeMData
  unless a.isAppOf ``Bind.bind && a.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let first := a.getAppArgs[a.getAppArgs.size-2]!.consumeMData
  let expected ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo name
  unless first.isAppOf expected do Lean.throwError "different first action"

elab "rx_stack_step" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let t := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := t.getAppArgs
  unless t.isAppOf ``Hoare && args.size ≥ 3 do Lean.throwError "not a Hoare contract"
  let a := args[args.size-3]!.consumeMData
  unless a.isAppOf ``Bind.bind && a.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let aa := a.getAppArgs
  let first := aa[aa.size-2]!
  let tail := aa.back!
  let pre := args[args.size-2]!
  let htype ← Lean.Meta.mkAppM ``Preserves #[pre,first]
  let h ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar htype
  let .forallE name dom _ _ ← Lean.Meta.inferType tail | Lean.throwError "not a continuation"
  let nextType ← Lean.Meta.withLocalDeclD name dom fun x => do
    let target ← Lean.Meta.mkAppM ``Hoare #[Lean.mkApp tail x,pre,args.back!]
    Lean.Meta.mkForallFVars #[x] target
  let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar nextType
  let proof ← Lean.Meta.mkAppM ``hoare_bind #[first,tail,h,next]
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal [h.mvarId!,next.mvarId!]

macro "rx_stack_return" : tactic => `(tactic|
  (index_material_head Pure.pure
   unfold Hoare
   apply Triple.pure
   intro w
   exact SPred.pure_mono (fun hi => hi)))

theorem txSelect_pending (initial : WGWorld) (family : Nat) (ps : List WG.Packet) (mtu : Nat) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer w⌝⦄ Packets.txSelect family ps mtu peer
    ⦃⇓? result w => ⌜SelectedXmit initial result w⌝⦄ := by
  have branch_rule {α : Type} (d : Decision) (value : Bool) (f : Bool → WG.M α)
      (P : WGWorld → Prop) (Q : α → WGWorld → Prop) (hf : Hoare (f value) P Q) :
      Hoare (branch d value >>= f) P Q := by
    apply hoare_bind _ _ (branch_predicate_native P d value)
    intro result
    apply (hoare_iff_run_ambient _ _ _).mpr
    rintro w ambient x v ambient' ⟨rfl,hi⟩ hr
    exact (hoare_iff_run_ambient _ _ _).mp hf w ambient x v ambient' hi hr
  have getter (P : WGWorld → Prop) (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    obtain ⟨rfl,_,_⟩ := getPeer_normal pid w v p ambient ambient' hr
    exact hi
  have errors := fun ret => closed_frame (project := id)
    (txError_reply family (ps.head?.getD {bytes := []}) ret) initial
  cases peer with
  | none =>
    have body : Hoare (Packets.txSelect family ps mtu none) (XmitClosed initial)
        (fun result w => SelectedXmit initial result w) := by
      unfold Packets.txSelect
      apply branch_rule
      simp only [Option.isNone_none,ite_true]
      material_lower
      repeat' first
        | unfold Preserves
        | (index_material_head Packets.txError; exact errors _)
        | rx_stack_step
        | rx_stack_return
        | material_component
        | material_join
        | material_join_use
        | material_intro
        | (index_material_head ite; split)
        | material_reduce
        | material_match
    exact hoare_consequence body (fun _ h => ⟨h.2,h.1⟩) (fun _ _ h => h)
  | some pid =>
    change Hoare _ (XmitPending initial (some pid)) (fun result w => SelectedXmit initial result w)
    unfold Packets.txSelect
    apply branch_rule
    simp only [Option.isNone_some,Bool.false_eq_true,ite_false]
    unfold WG.andM envOk
    material_lower
    repeat' first
      | unfold Preserves
      | (rx_stack_bind_head peerPut
         apply hoare_bind _ _ (pending_repay initial (some pid))
         intro x)
      | (index_material_head Packets.txError; exact errors _)
      | (index_material_head Lifetimes.xmitTrim
         exact pending_frame (project := id)
           (reply_views (project := id) (xmitTrim_protect pid) (xmitTrim_keyView pid)) initial (some pid))
      | (index_material_head Packets.txWalk
         exact pending_frame (project := id) (reply_kernel (project := id) (txWalk_kernel ps mtu [])) initial (some pid))
      | (index_material_head getPeer; exact getter _ _)
      | rx_stack_step
      | rx_stack_return
      | material_component
      | material_join
      | material_join_use
      | material_intro
      | (index_material_head ite; split)
      | material_reduce
      | material_match
      | contradiction

theorem txFinish_closed (initial : WGWorld) (pid : PeerId) (ps : List WG.Packet) :
    ⦃fun w => ⌜XmitPending initial (some pid) w⌝⦄ Packets.txFinish pid ps
    ⦃⇓? _ w => ⌜XmitClosed initial w⌝⦄ := by
  have splice := pending_frame (project := id)
    (reply_views (project := id) (xmitSplice_protect pid ps) (xmitSplice_keyView pid ps)) initial (some pid)
  unfold Packets.txFinish
  apply hoare_bind _ _ splice
  intro _
  apply hoare_bind _ _ (pending_stage initial pid)
  intro _
  apply hoare_bind _ _ (pending_repay initial (some pid))
  intro _
  exact preserves_pure _

/-- The original destination lookup funds its loan. All normal transmit
statuses, including negative errno, repay it without discarding durable delta. -/
theorem wgXmit_closed (family addr : Nat) (ps : List WG.Packet) (mtu : Nat)
    (hc : CurrentsCompatible w)
    (hr : ((wgXmit family addr ps mtu).run w).run ambient=.ok ((ret,v),ambient')) :
    XmitClosed w v := by
  rw [Packets.wgXmit_factor] at hr
  obtain ⟨checked,u,a,hcheck,tail⟩ := bind_ok_native hr
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp
    (txCheck_reply family addr ps mtu) w ambient checked u a hcheck
  have hu : XmitClosed w u := xmitClosed_view ⟨Transfer.refl w,hc⟩ view
  cases checked with
  | false =>
    simp at tail
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := tail
    exact hu
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨peer,b,ab,hlookup,tail⟩ := bind_ok_native tail
    have pending := lookup_pending family addr hu.2 hlookup
    obtain ⟨selected,c,ac,hselect,tail⟩ := bind_ok_native tail
    have selectedInv := (hoare_iff_run_ambient _ _ _).mp
      (txSelect_pending u family ps mtu peer) b ab selected c ac pending hselect
    have closed : XmitClosed u v := by
      cases selected with
      | error e =>
        simp at tail
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := tail
        exact selectedInv
      | ok pair =>
        exact (hoare_iff_run_ambient _ _ _).mp
          (txFinish_closed u pair.1 pair.2) c ac ret v ambient' selectedInv tail
    exact ⟨hu.1.trans closed.1,closed.2⟩

/-- Compatible RX/current words and the exact source-created durable transfer.
This normal-endpoint contract neither asserts socket delivery nor totality. -/
def StackState (initial w : WGWorld) : Prop := Transfer initial w ∧ KeysCompatible w

theorem keys_kernel (hk : wgStoreView v=wgStoreView w) (hi : KeysCompatible w) : KeysCompatible v := by
  have hd : v.dev=w.dev := congrArg WGStoreView.dev hk
  simpa only [KeysCompatible,RxCompatible,CurrentsCompatible,CurrentCompatible,KeyCompatible,hd] using hi

theorem stackState_kernel (initial : WGWorld) :
    KernelStable (fun w : World => StackState initial w.wg) := by
  intro w v hk hi
  have hwg : wgStoreView v.wg=wgStoreView w.wg := congrArg (fun s : ProductStore43 => s.2.2.2) hk
  refine ⟨hi.1.after_view ?_,keys_kernel hwg hi.2⟩
  have hd : v.wg.dev=w.wg.dev := congrArg WGStoreView.dev hwg
  unfold protectView peerView rxView handoffTxView sendView
  rw [hd]

theorem kernel_predicate {P : World → Prop} {a : Leanux.M α}
    (hp : KernelStable P) (ha : SameProductStore a) :
    ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact hp w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem stackState_call (a : Leanux.M α)
    (ha : ∀ w x v, KeysCompatible w.wg → a.run w=.ok (x,v) → StackState w.wg v.wg)
    (initial : WGWorld) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ a ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have h := ha w x v hi.2 hr
  exact ⟨hi.1.trans h.1,h.2⟩

theorem wgXmit_protection (family addr : Nat) (ps : List WG.Packet) (mtu : Nat)
    (hi : KeysCompatible w)
    (hr : ((wgXmit family addr ps mtu).run w).run ambient=.ok ((ret,v),ambient')) :
    StackState w v := by
  have hc := wgXmit_closed family addr ps mtu hi.2 hr
  have hk := (KeyEffects.iff_run_ambient _ _).mp
    (wgXmit_keyEffect (allowed:=NoPromotion) family addr ps mtu) w ambient ret v ambient' hr
  obtain ⟨delta,hd⟩ := hc.1
  exact ⟨⟨delta,hd⟩,hk.rxCompatible hd.rx hi.1,hc.2⟩

elab "rx_stack_lift_head" : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let args := t.getAppArgs
  unless t.isAppOf ``Hoare && args.size ≥ 3 do Lean.throwError "not a Hoare contract"
  let a := args[args.size-3]!.consumeMData
  unless [``MonadLift.monadLift,``MonadLiftT.monadLift,``monadLift,``liftM,
      ``liftWG,``liftAmbient].any a.isAppOf do Lean.throwError "not a component lift"

elab "rx_stack_lift_source " name:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let args := t.getAppArgs
  unless t.isAppOf ``Hoare && args.size ≥ 3 do Lean.throwError "not a Hoare contract"
  let mut a := args[args.size-3]!.consumeMData
  let lifts := [``MonadLift.monadLift,``MonadLiftT.monadLift,``monadLift,``liftM,
    ``liftWG,``liftRouting,``liftAmbient]
  unless lifts.any a.isAppOf do Lean.throwError "not a component lift"
  for _ in [:8] do
    if lifts.any a.isAppOf then
      let aa := a.getAppArgs
      unless aa.size > 0 do Lean.throwError "lift has no source"
      a := aa.back!.consumeMData
  let expected ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo name
  unless a.isAppOf expected do Lean.throwError "different lifted source"

theorem reply4_stack (initial : WGWorld) (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  let P := fun w : World => StackState initial w.wg
  have transmit (family addr : Nat) (ps : List WG.Packet) (mtu : Nat) :
      Preserves P (liftWG (wgXmit family addr ps mtu)) := by
    apply stackState_call
    intro w ret v hi hr
    rw [liftWG_run] at hr
    cases hn : ((wgXmit family addr ps mtu).run w.wg).run w.ambient with
    | error e => simp [hn,Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨r,g⟩,ambient⟩
      simp [hn,Except.map] at hr
      rcases hr with ⟨rfl,rfl⟩
      exact wgXmit_protection family addr ps mtu hi hn
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate (stackState_kernel initial)
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have device : Preserves P (liftWG getDev) :=
    kernel_predicate (stackState_kernel initial) (liftWG_sameProductStore _ getDev_sameWGStore)
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.reply4 skipCut
  material_lower
  repeat' first
    | (rx_stack_lift_source wgXmit; exact transmit _ _ _ _)
    | (rx_stack_lift_source getDev; exact device)
    | (first | rx_stack_lift_source Net.routeOutput4 | rx_stack_lift_source Net.neighbourClassify
       exact routing _)
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem receive4_stack (initial : WGWorld) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  let P := fun w : World => StackState initial w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate (stackState_kernel initial)
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.receive4 Leanux.Env.Stack.excluded
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.reply4; exact reply4_stack initial _ _)
    | (index_material_head getWG; exact read)
    | (index_material_head modifyEnv; exact write _)
    | (rx_stack_lift_source Net.routeInput4; exact routing _)
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem stackReceive_stack (initial : WGWorld) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  let P := fun w : World => StackState initial w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.receive
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.receive4; exact receive4_stack initial _)
    | (index_material_head Leanux.Env.Stack.receive6
       exact kernel_predicate (stackState_kernel initial) (stackReceive6_sameKernel _))
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem deliverInner_stack (initial : WGWorld) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  change Hoare _ (fun w : World => StackState initial w.wg) (fun _ w => StackState initial w.wg)
  unfold Leanux.Env.deliverInner
  exact stackReceive_stack initial bytes

theorem stackForM_stack (initial : WGWorld) (packets : List (List UInt8)) :
    ⦃fun w => ⌜StackState initial w.wg⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes xs ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_stack initial bytes) (fun _ => ih)

/-- The same supplied RX ledger and reservations survive actual Stack batches.
The added reservations are exactly the source-attributed TX/send-work delta. -/
theorem stackForM_protection (packets : List (List UInt8))
    (hi : Inventory cs w.wg) (hq : QueueOwners cs w.wg)
    (hp : Protected cs loans w.wg) (hk : KeysCompatible w.wg)
    (hr : (packets.forM Leanux.Env.deliverInner).run w=.ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧ Inventory cs v.wg ∧ QueueOwners cs v.wg ∧
      Protected cs loans v.wg ∧ Protected cs (loans++delta.owners) v.wg ∧ KeysCompatible v.wg := by
  have out := (hoare_iff_run _ _ _).mp (stackForM_stack w.wg packets)
    w () v ⟨Transfer.refl w.wg,hk⟩ hr
  obtain ⟨delta,hd⟩ := out.1
  obtain ⟨hin,hqn,hpn,hpd⟩ := hd.protect hi hq hp
  exact ⟨delta,hd,hin,hqn,hpn,hpd,out.2⟩

end Leanux.Proofs.WG.Queues.RxCredits
