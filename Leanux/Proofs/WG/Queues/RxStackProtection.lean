import Leanux.Proofs.WG.Queues.RxKeyProtection

/-! Actual stack replies preserve a supplied RX carrier ledger. The destination
lookup supplies its own positive reference loan; repayment retains any typed
TX/send-work handoff made by the concrete staged-send call. Normal error codes
are included. No stack success, peer residency or failed World is assumed. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
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
    (hr : (peerPut (some o.slot)).run u=.ok ((),v)) : Handoff w v [] [] delta := by
  have hc := h.count o
  simp only [List.count_cons_self,List.count_nil,Nat.add_zero] at hc
  have hu : 1<balance u o := by omega
  cases hp : resident u o with
  | none => simp [balance,hp] at hu
  | some p =>
    obtain ⟨d,hd,he,hs,ht⟩ := resident_fields hp
    have count : 1<p.refcount := by simpa [balance,hp] using hu
    have ho : o=⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
    have paid := peerPut_handoff hd hs count hr
    rw [←ho] at paid
    simpa [HandoffDelta.append] using h.trans paid

theorem borrowed_keyView (h : PeerBorrow.Borrowed w.k result v.k) : keyView v=keyView w := by
  cases result with
  | none => unfold keyView keyWords currentCells; rw [h]
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv⟩ := h
    apply keyView_affiliation
    simp only [Affiliation.view,hv,hd,Option.map_some]
    exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount:=p.refcount+1} hp rfl)

theorem lookupDst_keyView (family addr : Nat) : SameView keyView (lookupDst family addr) := by
  intro w result v hr
  exact borrowed_keyView ((hoare_iff_triple _ _ _).mpr (RxBorrow.lookupDst_spec family addr w.k) w result v rfl hr)

theorem xmitTrim_keyView (pid : PeerId) : SameView keyView (Lifetimes.xmitTrim pid) := by
  apply SameView.of_wp; intro s
  have hg := getPeer_key_spec (fun t => t=s) pid
  have hs := setPeer_key_spec (fun t => t=s) pid
  have hd := (modifyDev_keyView (fun d => {d with txDropped:=d.txDropped+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  have hl (α β : Type) := list_view_spec keyView (α:=α) (β:=β) (fun t => t=s)
  simp only [Lifetimes.xmitTrim,Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,hd,branch]
  all_goals try exact ((⇓? _ w => ⌜keyView w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold keyView keyWords currentCells at *
  all_goals simp_all [currentCell,Option.map_map,Option.bind_map,Function.comp_def]

theorem xmitSplice_keyView (pid : PeerId) (packets : List WG.Packet) : SameView keyView (Lifetimes.xmitSplice pid packets) := by
  simp only [Lifetimes.xmitSplice,getPeer_twice]
  exact modifyPeer_keyView pid (fun p => {p with staged:=p.staged++packets}) (fun _ => rfl)

theorem wgXmit_keyEffect (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    KeyEffects allowed (wgXmit family addr packets mtu) := by
  rw [Lifetimes.wgXmitSource_eq]
  apply keyEffects_of_wp; intro initial
  have hl := (keyEffects_view (allowed:=allowed) (lookupDst_keyView family addr)).wp initial
  have ht := fun pid => (keyEffects_view (allowed:=allowed) (xmitTrim_keyView pid)).wp initial
  have hs := fun pid ps => (keyEffects_view (allowed:=allowed) (xmitSplice_keyView pid ps)).wp initial
  have hstage := fun pid => (staged_send_keyEffect (allowed:=allowed) pid).wp initial
  have hp := fun pid => (peerPut_keyEffect (allowed:=allowed) pid).wp initial
  have hloop := fun sites raised => (keyEffects_view (allowed:=allowed) (keyView_kernel (loopbackSend_kernel sites raised))).wp initial
  have hcut := fun sites => (keyEffects_view (allowed:=allowed) (keyView_kernel (skipCutSites_sameKernel sites))).wp initial
  have henv := fun site => (keyEffects_view (allowed:=allowed) (keyView_kernel (envOk_sameKernel site))).wp initial
  have herr := (keyEffects_view (allowed:=allowed) (modifyDev_keyView
    (fun d => {d with txErrors:=d.txErrors+1}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))).wp initial
  have hlist (α β : Type) := list_view_spec keyView (α:=α) (β:=β) (KeyRelation allowed (keyView initial))
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hlist,Lifetimes.wgXmitSource,
    hl,ht,hs,hstage,hp,hloop,hcut,henv,herr,WG.andM,getPeer,getDev,getK,branch,invariant,unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyEffect,keyView]
  all_goals try (unfold keyWords currentCells at *; simp_all)

def replyView (w : World) := (protectView w,keyView w)
theorem reply_kernel (ha : SameKernel a) : SameView replyView a :=
  fun w x v hr => Prod.ext (protect_kernel ha w x v hr) (keyView_kernel ha w x v hr)
theorem reply_views (hp : SameView protectView a) (hk : SameView keyView a) : SameView replyView a :=
  fun w x v hr => Prod.ext (hp w x v hr) (hk w x v hr)

theorem currents_view (h : keyView v=keyView w) (hc : CurrentsCompatible w) : CurrentsCompatible v :=
  (keyEffect_of_view (allowed:=NoPromotion) h).currentsCompatible hc (fun _ _ h => False.elim h)

/-- Outstanding source-attributed destination loan. `none` has no loan; the
positive source balance is retained through the exact same accumulated delta. -/
def XmitPending (initial : World) (peer : Option PeerId) (w : World) : Prop :=
  CurrentsCompatible w ∧ match peer with
  | none => Transfer initial w
  | some pid => ∃o, o.slot=pid ∧ 0<balance initial o ∧ ∃delta,Handoff initial w [] [o] delta
def XmitClosed (initial w : World) : Prop := Transfer initial w ∧ CurrentsCompatible w

theorem xmitPending_view (h : XmitPending initial peer w) (he : replyView v=replyView w) : XmitPending initial peer v := by
  refine ⟨currents_view (congrArg Prod.snd he) h.1,?_⟩
  cases peer with
  | none => exact h.2.after_view (congrArg Prod.fst he)
  | some pid =>
    obtain ⟨o,ho,pos,d,hd⟩ := h.2
    exact ⟨o,ho,pos,d,hd.after_view (congrArg Prod.fst he)⟩

theorem xmitClosed_view (h : XmitClosed initial w) (he : replyView v=replyView w) : XmitClosed initial v :=
  ⟨h.1.after_view (congrArg Prod.fst he),currents_view (congrArg Prod.snd he) h.2⟩

theorem pending_frame (ha : SameView replyView a) (initial : World) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer w⌝⦄ a ⦃⇓? _ w => ⌜XmitPending initial peer w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr; exact xmitPending_view hi (ha w x v hr)

theorem closed_frame (ha : SameView replyView a) (initial : World) :
    ⦃fun w => ⌜XmitClosed initial w⌝⦄ a ⦃⇓? _ w => ⌜XmitClosed initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr; exact xmitClosed_view hi (ha w x v hr)

theorem pending_repay (initial : World) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer w⌝⦄ peerPut peer
    ⦃⇓? _ w => ⌜XmitClosed initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases x
  have effect := peerPut_keyEffect (allowed:=NoPromotion) peer w () v hr
  refine ⟨?_,effect.currentsCompatible hi.1 (fun _ _ h => False.elim h)⟩
  cases peer with
  | none =>
    have hk : v.k=w.k := by
      have hn : SameKernel (peerPut none) := by
        apply sameKernel_of_wp; intro k
        mvcgen [peerPut,branch,invariant]
      exact hn w () v hr
    exact hi.2.after_view (by unfold protectView peerView rxView handoffTxView sendView; rw [hk])
  | some pid =>
    obtain ⟨o,ho,pos,d,hd⟩ := hi.2
    exact ⟨d,repay_handoff_delta hd pos (by simpa [ho] using hr)⟩

theorem pending_stage (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜XmitPending initial (some pid) w⌝⦄ sendStagedPackets pid
    ⦃⇓? _ w => ⌜XmitPending initial (some pid) w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases x
  obtain ⟨o,ho,pos,d,hd⟩ := hi.2
  obtain ⟨new,hn⟩ := staged_send_handoff pid (hi.1 pid) hr
  have effect := staged_send_keyEffect (allowed:=NoPromotion) pid w () v hr
  refine ⟨effect.currentsCompatible hi.1 (fun _ _ h => False.elim h),o,ho,pos,d.append new,?_⟩
  exact hd.trans (by simpa using hn.with_loans [o])

theorem modifyDev_reply (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers)
    (hk : ∀d,(f d).keypairs=d.keypairs) (hr : ∀d,(f d).rxSkbs=d.rxSkbs)
    (hs : ∀d,(f d).sendWorkQueue=d.sendWorkQueue) : SameView replyView (modifyDev f) :=
  reply_views (modifyDev_protect f he hp hr hs) (modifyDev_keyView f he hp hk)

theorem xmitTrim_protect (pid : PeerId) : SameView protectView (Lifetimes.xmitTrim pid) := by
  apply SameView.of_wp; intro s
  have hg := getPeer_protect_spec (fun t => t=s) pid
  have hs := setPeer_protect_spec (fun t => t=s) pid
  have hd := (modifyDev_protect (fun d => {d with txDropped:=d.txDropped+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  have hl (α β : Type) := list_view_spec protectView (α:=α) (β:=β) (fun t => t=s)
  simp only [Lifetimes.xmitTrim,Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,hd,branch]
  all_goals try exact ((⇓? _ w => ⌜protectView w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold protectView peerView rxView handoffTxView sendView at *
  all_goals simp_all [protectCell,Option.map_map,Option.bind_map,Function.comp_def]

theorem xmitSplice_protect (pid : PeerId) (ps : List WG.Packet) : SameView protectView (Lifetimes.xmitSplice pid ps) := by
  simp only [Lifetimes.xmitSplice,getPeer_twice]
  exact modifyPeer_protect pid (fun p => {p with staged:=p.staged++ps}) (fun _ => rfl)

theorem txHeaders_kernel (family addr : Nat) (ps : List WG.Packet) : SameKernel (Packets.txHeaders family addr ps) := by
  apply sameKernel_of_wp; intro k
  have hl (α β : Type) := list_view_spec (fun w : World => w.k) (α:=α) (β:=β) (fun t => t=k)
  mvcgen [Packets.txHeaders,-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,invariant]

theorem txWalk_kernel (ps : List WG.Packet) (mtu : Nat) (acc : List WG.Packet) : SameKernel (Packets.txWalk ps mtu acc) := by
  apply sameKernel_of_wp; intro k
  have hl (α β : Type) := list_view_spec (fun w : World => w.k) (α:=α) (β:=β) (fun t => t=k)
  mvcgen [Packets.txWalk,-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,branch]

theorem txCheck_reply (family addr : Nat) (ps : List WG.Packet) (mtu : Nat) : SameView replyView (Packets.txCheck family addr ps mtu) := by
  apply SameView.of_wp; intro s
  have hh := (reply_kernel (txHeaders_kernel family addr ps)).wp (fun t => t=s)
  have he := (modifyDev_reply (fun d => {d with txErrors:=d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [Packets.txCheck,hh,he,WG.andM,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold replyView protectView peerView rxView handoffTxView sendView keyView keyWords currentCells at *
  all_goals simp_all

theorem txError_reply (family : Nat) (ret : Int) : SameView replyView (Packets.txError family ret) := by
  apply SameView.of_wp; intro s
  have hc := fun sites => (reply_kernel (skipCutSites_sameKernel sites)).wp (fun t => t=s)
  have hl := fun sites raised => (reply_kernel (loopbackSend_kernel sites raised)).wp (fun t => t=s)
  have he := (modifyDev_reply (fun d => {d with txErrors:=d.txErrors+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [Packets.txError,hc,hl,he,branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold replyView protectView peerView rxView handoffTxView sendView keyView keyWords currentCells at *
  all_goals simp_all

theorem lookup_pending (family addr : Nat) (hc : CurrentsCompatible w)
    (hr : (lookupDst family addr).run w=.ok (peer,v)) : XmitPending w peer v := by
  have hb := (hoare_iff_triple _ _ _).mpr (RxBorrow.lookupDst_spec family addr w.k) w peer v rfl hr
  refine ⟨currents_view (borrowed_keyView hb) hc,?_⟩
  cases peer with
  | none =>
    exact (Transfer.refl w).after_view (by unfold protectView peerView rxView handoffTxView sendView; rw [hb])
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv⟩ := hb
    refine ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,by simp [balance,resident,hd,hp,pos],{},?_⟩
    apply (acquire_handoff hd hp).after_view
    unfold protectView peerView rxView handoffTxView sendView
    simp [creditKernel,hv]

def SelectedXmit (initial : World) (result : Except Int (PeerId × List WG.Packet)) (w : World) : Prop :=
  match result with
  | .error _ => XmitClosed initial w
  | .ok (pid,_) => XmitPending initial (some pid) w

theorem txSelect_pending (initial : World) (family : Nat) (ps : List WG.Packet) (mtu : Nat) (peer : Option PeerId) :
    ⦃fun w => ⌜XmitPending initial peer w⌝⦄ Packets.txSelect family ps mtu peer
    ⦃⇓? result w => ⌜SelectedXmit initial result w⌝⦄ := by
  cases peer with
  | none =>
    have he := fun ret => closed_frame (txError_reply family ret) initial
    have hb := branch_predicate (XmitPending initial none) (by
      intro w v hk hi; exact xmitPending_view hi (by unfold replyView protectView peerView rxView handoffTxView sendView keyView keyWords currentCells; rw [hk]))
    mvcgen [Packets.txSelect,he,hb,invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [SelectedXmit,XmitPending,XmitClosed]
  | some pid =>
    have hp := pending_repay initial (some pid)
    have he := fun ret => closed_frame (txError_reply family ret) initial
    have ht := pending_frame (reply_views (xmitTrim_protect pid) (xmitTrim_keyView pid)) initial (some pid)
    have hw := pending_frame (reply_kernel (txWalk_kernel ps mtu [])) initial (some pid)
    have hen := pending_frame (reply_kernel (envOk_sameKernel .skbSegment)) initial (some pid)
    have hb := branch_predicate (XmitPending initial (some pid)) (by
      intro w v hk hi; exact xmitPending_view hi (by unfold replyView protectView peerView rxView handoffTxView sendView keyView keyWords currentCells; rw [hk]))
    mvcgen [Packets.txSelect,hp,he,ht,hw,hen,hb,WG.andM,getPeer,getDev,getK,invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [SelectedXmit]

theorem txFinish_closed (initial : World) (pid : PeerId) (ps : List WG.Packet) :
    ⦃fun w => ⌜XmitPending initial (some pid) w⌝⦄ Packets.txFinish pid ps
    ⦃⇓? _ w => ⌜XmitClosed initial w⌝⦄ := by
  have hs := pending_frame (reply_views (xmitSplice_protect pid ps) (xmitSplice_keyView pid ps)) initial (some pid)
  have ht := pending_stage initial pid
  have hp := pending_repay initial (some pid)
  mvcgen [Packets.txFinish,hs,ht,hp]

/-- The original destination lookup funds its loan. All normal transmit
statuses, including negative errno, repay it without discarding durable delta. -/
theorem wgXmit_closed (family addr : Nat) (ps : List WG.Packet) (mtu : Nat)
    (hc : CurrentsCompatible w) (hr : (wgXmit family addr ps mtu).run w=.ok (ret,v)) : XmitClosed w v := by
  rw [Packets.wgXmit_factor] at hr
  obtain ⟨checked,u,hcheck,tail⟩ := bind_ok hr
  have view := txCheck_reply family addr ps mtu w checked u hcheck
  have hu : XmitClosed w u := xmitClosed_view ⟨Transfer.refl w,hc⟩ view
  cases checked with
  | false =>
    simp at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact hu
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨peer,b,hlookup,tail⟩ := bind_ok tail
    have pending := lookup_pending family addr hu.2 hlookup
    obtain ⟨selected,c,hselect,tail⟩ := bind_ok tail
    have selectedInv := (hoare_iff_triple _ _ _).mpr (txSelect_pending u family ps mtu peer) b selected c pending hselect
    have closed : XmitClosed u v := by
      cases selected with
      | error e =>
        simp at tail; obtain ⟨rfl,rfl⟩ := tail
        exact selectedInv
      | ok pair =>
        exact (hoare_iff_triple _ _ _).mpr (txFinish_closed u pair.1 pair.2) c ret v selectedInv tail
    exact ⟨hu.1.trans closed.1,closed.2⟩

/-- Compatible RX/current words and the exact source-created durable transfer.
This normal-endpoint contract neither asserts socket delivery nor totality. -/
def StackState (initial w : World) : Prop := Transfer initial w ∧ KeysCompatible w

theorem keys_kernel (hk : v.k=w.k) (hi : KeysCompatible w) : KeysCompatible v := by
  simpa only [KeysCompatible,RxCompatible,CurrentsCompatible,CurrentCompatible,KeyCompatible,hk] using hi

theorem stackState_kernel (initial : World) : KernelStable (StackState initial) := by
  intro w v hk hi
  refine ⟨hi.1.after_view ?_,keys_kernel hk hi.2⟩
  unfold protectView peerView rxView handoffTxView sendView; rw [hk]

theorem kernel_predicate (hp : KernelStable P) (ha : SameKernel a) :
    ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  exact hp w v (ha w x v hr) hi

theorem stackState_call (a : M α)
    (ha : ∀ w x v, KeysCompatible w → a.run w=.ok (x,v) → StackState w v)
    (initial : World) :
    ⦃fun w => ⌜StackState initial w⌝⦄ a ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  have h := ha w x v hi.2 hr
  exact ⟨hi.1.trans h.1,h.2⟩

theorem wgXmit_protection (family addr : Nat) (ps : List WG.Packet) (mtu : Nat)
    (hi : KeysCompatible w) (hr : (wgXmit family addr ps mtu).run w=.ok (ret,v)) : StackState w v := by
  have hc := wgXmit_closed family addr ps mtu hi.2 hr
  have hk := wgXmit_keyEffect (allowed:=NoPromotion) family addr ps mtu w ret v hr
  obtain ⟨delta,hd⟩ := hc.1
  exact ⟨⟨delta,hd⟩,hk.rxCompatible hd.rx hi.1,hc.2⟩

theorem reply4_stack (initial : World) (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  have hx := fun family addr ps mtu => stackState_call (wgXmit family addr ps mtu)
    (fun _ _ _ hi hr => wgXmit_protection family addr ps mtu hi hr) initial
  have hc := fun sites => kernel_predicate (stackState_kernel initial) (skipCut_sameKernel sites)
  have hd (α : Type) := discard_view_spec id (α:=α) (StackState initial)
  mvcgen [Leanux.Env.Stack.reply4,hx,hc,hd,getDev,getK,invariant]

theorem receive4_stack (initial : World) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  have hr := reply4_stack initial
  mvcgen [Leanux.Env.Stack.receive4,Leanux.Env.Stack.excluded,hr,getK,invariant,unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals first | assumption | (rename_i s hi t; exact stackState_kernel initial s _ rfl hi)

theorem stackReceive_stack (initial : World) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  have h4 := receive4_stack initial bytes
  have h6 := kernel_predicate (stackState_kernel initial) (stackReceive6_sameKernel bytes)
  mvcgen [Leanux.Env.Stack.receive,h4,h6,invariant]

theorem deliverInner_stack (initial : World) (bytes : List UInt8) :
    ⦃fun w => ⌜StackState initial w⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  have hs := stackReceive_stack initial bytes
  mvcgen [Leanux.Env.deliverInner,hs]

theorem stackForM_stack (initial : World) (packets : List (List UInt8)) :
    ⦃fun w => ⌜StackState initial w⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜StackState initial w⌝⦄ := by
  induction packets with
  | nil => mvcgen
  | cons bytes xs ih =>
    have hb := deliverInner_stack initial bytes
    simp only [List.forM_eq_forM,List.forM_cons]
    mvcgen [hb,ih]

/-- The same supplied RX ledger and reservations survive actual Stack batches.
The added reservations are exactly the source-attributed TX/send-work delta. -/
theorem stackForM_protection (packets : List (List UInt8)) (hi : Inventory cs w) (hq : QueueOwners cs w)
    (hp : Protected cs loans w) (hk : KeysCompatible w)
    (hr : (packets.forM Leanux.Env.deliverInner).run w=.ok ((),v)) :
    ∃ delta, Handoff w v [] [] delta ∧ Inventory cs v ∧ QueueOwners cs v ∧
      Protected cs loans v ∧ Protected cs (loans++delta.owners) v ∧ KeysCompatible v := by
  have out := (hoare_iff_triple _ _ _).mpr (stackForM_stack w packets) w () v ⟨Transfer.refl w,hk⟩ hr
  obtain ⟨delta,hd⟩ := out.1
  obtain ⟨hin,hqn,hpn,hpd⟩ := hd.protect hi hq hp
  exact ⟨delta,hd,hin,hqn,hpn,hpd,out.2⟩

end Leanux.Proofs.WG.Queues.RxCredits
