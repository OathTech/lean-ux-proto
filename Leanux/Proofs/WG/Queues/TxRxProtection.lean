import Leanux.Proofs.WG.Queues.RxProtectionFrames
import Leanux.Proofs.WG.Queues.TxDisposal

/-! Source-acquired temporary references and concrete TX publication. Every
normal endpoint theorem refers to the original call; Stops have no final WGWorld. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option pp.structureInstances false

theorem bind_ok {S α β : Type} {a : StateT S (Except Stop) α} {f : α → StateT S (Except Stop) β}
    {w v : S} {y : β}
    (hr : (a >>= f).run w = .ok (y,v)) :
    ∃ x u, a.run w = .ok (x,u) ∧ (f x).run u = .ok (y,v) :=
  (MaterialOrigin.bind_ok _ _ _ _ _).mp hr

theorem bind_ok_native {α β : Type} {a : WG.M α} {f : α → WG.M β}
    {w v : WGWorld} {ambient ambient' : Ambient} {y : β}
    (hr : ((a >>= f).run w).run ambient = .ok ((y,v),ambient')) :
    ∃ x u midway, (a.run w).run ambient = .ok ((x,u),midway) ∧
      ((f x).run u).run midway = .ok ((y,v),ambient') :=
  (MaterialOrigin.bind_ok_ambient _ _ _ _ _ _ _).mp hr

/-- Closed attributed handoffs recover every field in the protection view. -/
private theorem closed_handoff_view (closed : Handoff w v [] [] {}) :
    protectView v = protectView w := by
  have hpv : peerView v = peerView w := by
    apply Prod.ext
    · simpa [peerView,baseView] using congrArg Prod.fst closed.base
    · funext q
      have hb := congrFun (congrArg Prod.snd closed.base) q
      cases hw : w.dev with
      | none =>
        have hv : v.dev = none := by
          have := congrArg Prod.fst closed.base
          simpa [baseView,hw] using this
        simp [peerView,hw,hv]
      | some dw =>
        cases hv : v.dev with
        | none =>
          have ep := congrArg Prod.fst closed.base
          simp [baseView,hw,hv] at ep
        | some dv =>
          have ep : dv.ifindex = dw.ifindex := by simpa [baseView,hw,hv] using congrArg Prod.fst closed.base
          cases pw : dw.peers[q]? <;> cases pv : dv.peers[q]? <;> simp_all [baseView,peerView]
          rename_i a b
          have cc := closed.count ⟨dw.ifindex,q,a.internalId⟩
          simp_all [balance,resident]
  unfold protectView
  refine Prod.ext hpv (Prod.ext closed.rx (Prod.ext ?_ ?_))
  · funext q; simpa using closed.tx q
  · simpa using closed.send

/-- The arbitrary middle retains product scope, including other subsystems
and Ambient. Only its protection-view frame is assumed. -/
theorem loan_middle_repay (pid : PeerId) (a : Leanux.M Unit)
    (ha : SameView (fun w => protectView w.wg) a) :
    SameView (fun w => protectView w.wg)
      (do liftWG (peerGet pid); a; liftWG (peerPut (some pid))) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  obtain ⟨x₁,u,hget,hr⟩ := bind_ok hr
  cases x₁
  obtain ⟨x₂,b,hmid,hput⟩ := bind_ok hr
  cases x₂
  cases x
  have native (action : WG.M Unit) (w v : World)
      (run : (liftWG action).run w = .ok ((),v)) :
      (action.run w.wg).run w.ambient = .ok (((),v.wg),v.ambient) := by
    rw [liftWG_run] at run
    cases hn : (action.run w.wg).run w.ambient with
    | error e => simp [hn,Except.map] at run
    | ok out =>
      rcases out with ⟨⟨u,g⟩,ambient⟩
      cases u
      simp [hn,Except.map] at run
      subst v
      rfl
  have getNative := native (peerGet pid) w u hget
  have putNative := native (peerPut (some pid)) b v hput
  obtain ⟨d,p,hd,hp,pos,h⟩ := peerGet_handoff _ _ getNative
  have hc := h.after_view ((ProjectedAction.iff_run _ _ _).mp ha u () b hmid)
  have old : 0 < balance w.wg ⟨d.ifindex,pid,p.internalId⟩ := by simp [balance,resident,hd,hp,pos]
  exact closed_handoff_view (repay_handoff hc old _ _ putNative)

/-- The native specialization carries both actual Ambient cuts through the
middle call, without restricting the product theorem's callback domain. -/
theorem loan_middle_repay_native (pid : PeerId) (a : WG.M Unit)
    (ha : SameView protectView a) :
    SameView protectView (do peerGet pid; a; peerPut (some pid)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  obtain ⟨u,a,ambientA,hget,hr⟩ := bind_ok_native hr
  cases u
  obtain ⟨u,b,ambientB,hmid,hput⟩ := bind_ok_native hr
  cases u
  cases x
  obtain ⟨d,p,hd,hp,pos,h⟩ := peerGet_handoff ambient ambientA hget
  have hc := h.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp ha a ambientA () b ambientB hmid)
  have old : 0 < balance w ⟨d.ifindex,pid,p.internalId⟩ := by simp [balance,resident,hd,hp,pos]
  exact closed_handoff_view (repay_handoff hc old ambientB ambient' hput)

theorem publicationMiddle_protect (pid : PeerId) (first : SkbId) (state : PacketState) :
    SameView protectView (TxDisposition.publicationMiddle pid first state) := by
  have getter : SameView protectView (getPeer pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal pid w v p ambient ambient' hr
    rfl
  have ambient {α : Type} (a : AmbientM α) :
      SameView protectView (monadLift a : WG.M α) := by
    intro initial
    exact hoare_liftAmbient a (fun w => protectView w = initial)
  have hm := modifyDev_protect (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  unfold TxDisposition.publicationMiddle
  simp only [invariant,peekQueuedUnit,recordQueued]
  repeat' first
    | dump_kernel_join_let
    | dump_kernel_join_use
    | (dump_kernel_head getPeer; exact getter)
    | (dump_kernel_head setTxSkb; exact setTx_protect first (fun p => {p with state}))
    | (dump_kernel_head cpumaskChooseOnline; exact cpu_protect pid)
    | (dump_kernel_head getDev; exact protect_kernel (project := id) getDev_sameWGStore)
    | (dump_kernel_head modifyDev; exact hm)
    | (dump_kernel_head monadLift; exact ambient _)
    | (dump_kernel_head Pure.pure; exact SameView.pure _ _)
    | (dump_kernel_head Bind.bind; apply SameView.bind)
    | dump_kernel_intro
    | (dump_kernel_head ite; split)
    | dump_dump_kernel_head_reduce
    | dump_dump_kernel_head_match

theorem publication_protect (item : List SkbId) (state : PacketState) :
    SameView protectView (enqueuePerPeerTx item state) := by
  rw [TxDisposition.publication_factor]
  cases hh : item.head? with
  | none =>
    simp only [invariant]
    intro initial
    exact hoare_liftAmbient _ (fun w => protectView w = initial)
  | some first =>
    apply SameView.bind (getTx_protect first)
    intro pkt
    apply SameView.bind (by
      intro initial
      exact indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun w => protectView w = initial))
    intro pid
    exact loan_middle_repay_native pid _ (publicationMiddle_protect pid first state)

/-- The concrete per-peer TX queue installation transfers one already supplied
loan into one batch occurrence; packet identifiers need not be distinct. -/
theorem installTx_handoff (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (item : List SkbId) :
    Handoff w {w with dev := some {d with peers := d.peers.insert pid {p with txQueue := p.txQueue.enqueue item}}}
      [⟨d.ifindex,pid,p.internalId⟩] [] {tx := [⟨⟨d.ifindex,pid,p.internalId⟩,item⟩]} := by
  constructor
  · unfold baseView
    simp [hd,Std.TreeMap.getElem?_insert,funext_iff]
    intro q; by_cases he : pid=q <;> simp_all
  · simp [rxView,hd]
  · intro q
    unfold handoffTxView HandoffDelta.items
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert,PrevQueue.enqueue,PrevQueue.all,List.append_assoc,Function.comp_def]
  · simp [sendView,hd]
  · intro o
    have hv : peerView {w with dev := some {d with peers := d.peers.insert pid {p with txQueue := p.txQueue.enqueue item}}} = peerView w := by
      unfold peerView
      simp [hd,funext_iff,Std.TreeMap.getElem?_insert]
      intro q; by_cases he : pid=q <;> simp_all
    rw [balance_view hv]
    simp [HandoffDelta.owners]

/-- The exact original enqueue setter at its reached source cut. The input
record is obtained by the original getter, not by a stale arbitrary setter. -/
theorem installTx_source (pid : PeerId) (item : List SkbId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.enqueue item}).run w).run ambient = .ok (((),v),ambient')) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
      Handoff w v [⟨d.ifindex,pid,p.internalId⟩] [] {tx := [⟨⟨d.ifindex,pid,p.internalId⟩,item⟩]} := by
  obtain ⟨p,u,midway,hget,hset⟩ := bind_ok_native hr
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w u p ambient midway hget
  cases hset
  exact ⟨d,p,hd,hp,by simpa [setPeer,modifyDev,hd] using installTx_handoff hd hp item⟩

/-- The actual staged acquisition fixes its caller from the resident nullable
word. NULL and missing owners retain their original Stops. -/
theorem sendAcquire_handoff (hc : KeyCompatible pid kid w) (ambient ambient' : Ambient)
    (hr : ((Affiliation.sendAcquire kid).run w).run ambient = .ok (((),v),ambient')) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Handoff w v [] [⟨d.ifindex,pid,p.internalId⟩] {} := by
  obtain ⟨d,k,actual,p,hd,hk,hw,hp,pos,hb⟩ := Affiliation.sendAcquire_certificate kid w v ambient ambient' hr
  have same : actual = pid := by simpa [Affiliation.Compatible,hw] using hc d k hd hk
  subst actual
  obtain ⟨e,q,he,hq,_,hv⟩ := hb
  have de : e=d := Option.some.inj (he.symm.trans hd)
  subst e
  have pq : q=p := Option.some.inj (hq.symm.trans hp)
  subst q
  have h := acquire_handoff (w:=w) hd hp
  refine ⟨d,p,hd,hp,pos,?_⟩
  apply h.after_view
  unfold protectView peerView rxView handoffTxView sendView
  have hdev := congrArg WGStoreView.dev hv
  change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at hdev
  simp only [creditWorld,hdev]

/-- Actual list allocation retains the already acquired loan; the packet list
and its output slot list are those of the original mapM, without extra getters. -/
theorem newTxList_protect (packets : List DataPacket) :
    SameView protectView (packets.mapM newTxSkb) := by
  induction packets with
  | nil => simpa using SameView.pure protectView ([] : List SkbId)
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact (newTx_protect p).bind fun _ => ih.bind fun _ => SameView.pure _ _

def OpenLoan (initial : WGWorld) (o : Owner) (current : WGWorld) : Prop :=
  Handoff initial current [] [o] {} ∧ 0 < balance initial o

theorem OpenLoan.resident (h : OpenLoan initial o w) :
    ∃ p, resident w o = some p ∧ 1 < p.refcount := by
  have hc := h.1.count o
  simp only [List.count_cons_self,List.count_nil,delta_empty_owners,Nat.add_zero] at hc
  have pos := h.2
  have hb : 1 < balance w o := by omega
  cases hp : RxCredits.resident w o with
  | none => simp [balance,hp] at hb
  | some p => exact ⟨p,rfl,by simpa [balance,hp] using hb⟩

theorem open_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => protectView (project s)) a) (initial : WGWorld) (o : Owner) :
    ⦃fun w => ⌜OpenLoan initial o (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜OpenLoan initial o (project w)⌝⦄ := by
  apply hoare_consequence
    (ha.wp (fun obs => ∃ w, OpenLoan initial o w ∧ obs = protectView w))
  · intro w hi; exact ⟨project w,hi,rfl⟩
  · intro x v hi
    obtain ⟨w,h,he⟩ := hi
    exact ⟨h.1.after_view he,h.2⟩

theorem open_getPeer (initial : WGWorld) (o : Owner) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ getPeer o.slot
    ⦃⇓? p w => ⌜OpenLoan initial o w ∧ resident w o = some p⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' h hr
  obtain ⟨old,hold,pos⟩ := h.resident
  obtain ⟨d,hd,he,hp,ht⟩ := resident_fields hold
  obtain ⟨rfl,_,d',hd',hp'⟩ := getPeer_normal o.slot w v p ambient ambient' hr
  have de : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  have pe : p = old := Option.some.inj (hp'.symm.trans hp)
  subst p
  exact ⟨h,hold⟩

theorem open_install (initial : WGWorld) (o : Owner) (p : Peer) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w ∧ resident w o = some p⌝⦄
      setPeer o.slot {p with txQueue := p.txQueue.enqueue item}
    ⦃⇓? _ w => ⌜Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  obtain ⟨d,hd,he,hp,ht⟩ := resident_fields h.2
  have ho : o = ⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
  have hi := installTx_handoff (w:=w) hd hp item
  rw [← ho] at hi
  cases hr
  simpa [HandoffDelta.append,setPeer,modifyDev,hd] using h.1.1.trans hi

theorem freeTxList_protect (item : List SkbId) : SameView protectView (TxDisposition.freeList item) := by
  induction item with
  | nil => simpa [TxDisposition.freeList_nil] using SameView.pure protectView ()
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact (freeTx_protect id).bind fun _ => ih

/-- The original createData cleanup consumes its previously acquired loan.
Its key put can Stop; the contract makes no claim about a failed endpoint. -/
theorem createCleanup_handoff (h : OpenLoan initial o w) (ambient ambient' : Ambient)
    (hr : ((TxDisposition.cleanupSource o.slot item first).run w).run ambient = .ok (((),v),ambient')) :
    Handoff initial v [] [] {} := by
  unfold TxDisposition.cleanupSource at hr
  obtain ⟨pkt,a,ambientA,hget,hr⟩ := bind_ok_native hr
  obtain ⟨_,b,ambientB,hkey,hr⟩ := bind_ok_native hr
  obtain ⟨_,c,ambientC,hpeer,hfree⟩ := bind_ok_native hr
  have hb := (h.1.after_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (getTx_protect first) w ambient pkt a ambientA hget)).after_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (keypairPut_protect (some pkt.keypair) false) a ambientA () b ambientB hkey)
  have hc := repay_handoff hb h.2 ambientB ambientC hpeer
  exact hc.after_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (freeTxList_protect item) c ambientC () v ambient' hfree)

/-- The original post-installation enqueue continuation, including ring installation. -/
def enqueueTailItem (item : List SkbId) : WG.M Int := do
  let d ← getDev
  let cpu ← cpumaskNextOnlineFrom d.encryptLastCpu
  modifyDev fun d => {d with encryptLastCpu := cpu}
  if ← branch .enqueueRingFull d.encryptQueue.full then return -EPIPE
  queueDeviceWork .encryptWorker
  modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce item}
  return 0

theorem enqueue_factor (pid : PeerId) (item : List SkbId) :
    enqueuePerDeviceAndPeer pid item = (do
      let some first := item.head? | invariant "an empty ring item"
      setTxSkb first fun p => {p with state := .uncrypted}
      let p ← getPeer pid
      if ← branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS) then return -ENOSPC
      setPeer pid {p with txQueue := p.txQueue.enqueue item}
      enqueueTailItem item) := by
  simp only [enqueuePerDeviceAndPeer,enqueueTailItem]
  rfl

/-- The original product predicate domain observes exactly the old 43 store
fields; predicates may still mention any part of the actual product World. -/
def KernelStable (P : World → Prop) : Prop :=
  ∀ w v, productStoreView v = productStoreView w → P w → P v

/-- Native stability retains the original seven-field WG mask. -/
def WGStoreStable (P : WGWorld → Prop) : Prop :=
  ∀ w v, wgStoreView v = wgStoreView w → P w → P v

theorem handoff_stable (initial : WGWorld) (before after : Reservations) (d : HandoffDelta) :
    WGStoreStable (fun w => Handoff initial w before after d) := by
  intro w v hk h
  apply h.after_view
  have hd := congrArg WGStoreView.dev hk
  change v.dev = w.dev at hd
  unfold protectView peerView rxView handoffTxView sendView
  rw [hd]

theorem open_stable (initial : WGWorld) (o : Owner) : WGStoreStable (OpenLoan initial o) := by
  intro w v hk h
  exact ⟨handoff_stable initial [] [o] {} w v hk h.1,h.2⟩

theorem branch_predicate (P : World → Prop) (hp : KernelStable P) (decision : Decision) (value : Bool) :
    ⦃fun w => ⌜P w⌝⦄ (branch decision value : Leanux.M Bool)
    ⦃⇓? result w => ⌜result = value ∧ P w⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v h hr
  change Except.ok (value,{w with ambient := CounterWindow.record w.ambient decision value}) =
    Except.ok (result,v) at hr
  cases hr
  exact ⟨rfl,hp w _ rfl h⟩

/-- In a native stack the recorded decision returns its supplied Boolean.
State preservation comes from the Ambient adapter, with no stability premise. -/
theorem branch_predicate_native {S : Type} (P : S → Prop) (decision : Decision) (value : Bool) :
    ⦃fun w => ⌜P w⌝⦄ (branch decision value : StateT S AmbientM Bool)
    ⦃⇓? result w => ⌜result = value ∧ P w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' h hr
  change Except.ok ((value,w),CounterWindow.record ambient decision value) =
    Except.ok ((result,v),ambient') at hr
  cases hr
  exact ⟨rfl,h⟩

theorem enqueueTailItem_spec (initial : WGWorld) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ enqueueTailItem item
    ⦃⇓? ret w => ⌜(ret = 0 ∨ ret = -EPIPE) ∧ Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient ret v ambient' h hr
  simp only [enqueueTailItem,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨d,a,aa,hget,cpu,b,ab,hcpu,u,c,ac,hset,full,e,ae,hbranch,hr⟩ := hr
  have ha := h.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (protect_kernel (project := id) getDev_sameWGStore) w ambient d a aa hget)
  have hb := ha.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (protect_kernel (project := id) (cpumaskNextOnlineFrom_sameStore d.encryptLastCpu))
    a aa cpu b ab hcpu)
  have hc := hb.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (modifyDev_protect (fun d => {d with encryptLastCpu := cpu})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) b ab u c ac hset)
  have he := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => Handoff initial g [] [] {tx := [⟨o,item⟩]})
      .enqueueRingFull d.encryptQueue.full) c ac full e ae hc hbranch).2
  cases full with
  | true =>
    simp only [ite_true] at hr
    cases hr
    exact ⟨Or.inr rfl,he⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,f,af,hqueue,u,g,ag,hproduce,hr⟩ := hr
    have hf := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker)
        (fun g => Handoff initial g [] [] {tx := [⟨o,item⟩]})) e ae u f af he hqueue
    have hg := hf.after_view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (modifyDev_protect (fun d => {d with encryptQueue := d.encryptQueue.produce item})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) f af u g ag hproduce)
    cases hr
    exact ⟨Or.inl rfl,hg⟩

theorem enqueue_open (initial : WGWorld) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ enqueuePerDeviceAndPeer o.slot item
    ⦃⇓? ret w => ⌜(ret = -ENOSPC ∧ OpenLoan initial o w) ∨
      ((ret = 0 ∨ ret = -EPIPE) ∧ Handoff initial w [] [] {tx := [⟨o,item⟩]})⌝⦄ := by
  rw [enqueue_factor]
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient ret v ambient' h hr
  cases head : item.head? with
  | none => simp only [head] at hr; cases hr
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,a,aa,hset,p,b,ab,hget,full,c,ac,hbranch,hr⟩ := hr
    have ha := (hoare_iff_run_ambient _ _ _).mp
      (open_frame (project := id) (setTx_protect first (fun p => {p with state := .uncrypted})) initial o)
      w ambient u a aa h hset
    have hb := (hoare_iff_run_ambient _ _ _).mp (open_getPeer initial o) a aa p b ab ha hget
    have hc := ((hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g => OpenLoan initial o g ∧ resident g o = some p)
        .enqueuePeerQueueFull (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS)))
      b ab full c ac hb hbranch).2
    cases full with
    | true =>
      simp only [ite_true] at hr
      cases hr
      exact Or.inl ⟨rfl,hc.1⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨u,e,ae,hinstall,htail⟩ := hr
      have he := (hoare_iff_run_ambient _ _ _).mp (open_install initial o p item) c ac u e ae hc hinstall
      exact Or.inr ((hoare_iff_run_ambient _ _ _).mp (enqueueTailItem_spec initial o item)
        e ae ret v ambient' he htail)


def CreateRet (initial : WGWorld) (o : Owner) (item : List SkbId) (ret : Int) (w : WGWorld) : Prop :=
  if ret = 0 ∨ ret = -EPIPE then Handoff initial w [] [] {tx := [⟨o,item⟩]}
  else OpenLoan initial o w

theorem createRet_stable (initial : WGWorld) (o : Owner) (item : List SkbId) (ret : Int) :
    WGStoreStable (CreateRet initial o item ret) := by
  unfold CreateRet
  split
  · exact handoff_stable _ _ _ _
  · exact open_stable _ _

theorem createTail_handoff (initial : WGWorld) (o : Owner) (item : List SkbId) (first : SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret w⌝⦄ TxDisposition.createTailSource o.slot item first ret
    ⦃⇓? _ w => ⌜∃ delta, Handoff initial w [] [] delta⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hi hr
  simp only [TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨ok,a,aa,hb,hr⟩ := hr
  have ha := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateRet initial o item ret) .createDataOk (ret == 0))
    w ambient ok a aa hi hb
  cases ok with
  | true =>
    simp only [ite_true] at hr
    cases hr
    have ret_zero : ret = 0 := by simpa using ha.1.symm
    exact ⟨{tx := [⟨o,item⟩]},by simpa [CreateRet,ret_zero] using ha.2⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨epipe,b,ab,hb,hr⟩ := hr
    have hb' := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (CreateRet initial o item ret) .createDataOkEpipe (ret == -WG.EPIPE))
      a aa epipe b ab ha.2 hb
    cases epipe with
    | true =>
      simp only [ite_true] at hr
      cases hr
      have ret_epipe : ret = -WG.EPIPE := by simpa using hb'.1.symm
      exact ⟨{tx := [⟨o,item⟩]},by simpa [CreateRet,ret_epipe,WG.EPIPE,EPIPE] using hb'.2⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false] at hr
      have ret_zero : ret ≠ 0 := by simpa using ha.1.symm
      have ret_epipe : ret ≠ -WG.EPIPE := by simpa using hb'.1.symm
      have loan : OpenLoan initial o b := by
        simpa [CreateRet,ret_zero,show ret ≠ -EPIPE from ret_epipe] using hb'.2
      exact ⟨{},createCleanup_handoff loan ab ambient' hr⟩

theorem createRet_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => protectView (project s)) a) (initial : WGWorld) (o : Owner)
    (item : List SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜CreateRet initial o item ret (project w)⌝⦄ := by
  unfold CreateRet
  split
  · exact handoff_frame_spec ha _ _ _ _
  · exact open_frame ha _ _

def createPublishReturn (item : List SkbId) (ret : Int) : WG.M Int := do
  if ← branch .createDataEpipe (ret == -WG.EPIPE) then enqueuePerPeerTx item .dead
  return ret

theorem createPublishReturn_spec (initial : WGWorld) (o : Owner) (item : List SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret w⌝⦄ createPublishReturn item ret
    ⦃⇓? result w => ⌜result = ret ∧ CreateRet initial o item ret w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨epipe,a,aa,hb,hr⟩ := hr
  have ha := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateRet initial o item ret) .createDataEpipe (ret == -WG.EPIPE))
    w ambient epipe a aa hi hb).2
  cases epipe with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hr
    cases hr
    exact ⟨rfl,ha⟩
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,b,ab,hp,hr⟩ := hr
    have hb := (hoare_iff_run_ambient _ _ _).mp
      (createRet_frame (project := id) (publication_protect item .dead) initial o item ret)
      a aa u b ab ha hp
    cases hr
    exact ⟨rfl,hb⟩

def createReturnSource (pid : PeerId) (item : List SkbId) : WG.M Int := do
  if ← branch .createDataDead (← getPeer pid).isDead then return -EINVAL
  let ret ← enqueuePerDeviceAndPeer pid item
  createPublishReturn item ret

theorem createReturn_spec (initial : WGWorld) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ createReturnSource o.slot item
    ⦃⇓? ret w => ⌜CreateRet initial o item ret w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient ret v ambient' hi hr
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,dead,b,ab,hb,hr⟩ := hr
  have ha := (hoare_iff_run_ambient _ _ _).mp (open_getPeer initial o)
    w ambient p a aa hi hget
  have hb' := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (OpenLoan initial o) .createDataDead p.isDead)
    a aa dead b ab ha.1 hb).2
  cases dead with
  | true =>
    simp only [ite_true] at hr
    cases hr
    simpa [CreateRet,EINVAL,EPIPE] using hb'
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨result,c,ac,henqueue,hpublish⟩ := hr
    have hc := (hoare_iff_run_ambient _ _ _).mp (enqueue_open initial o item)
      b ab result c ac hb' henqueue
    have retained : CreateRet initial o item result c := by
      rcases hc with ⟨rfl,h⟩ | ⟨returned,h⟩
      · simpa [CreateRet,ENOSPC,EPIPE] using h
      · simpa only [CreateRet,returned,ite_true] using h
    have last := (hoare_iff_run_ambient _ _ _).mp (createPublishReturn_spec initial o item result)
      c ac ret v ambient' retained hpublish
    simpa only [last.1] using last.2

theorem bind_if_source {m : Type → Type} [Monad m] (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = (if c then a >>= f else b >>= f) := by
  split <;> rfl

/-- Full original createData after its actual matched acquisition. -/
theorem createData_handoff (initial : WGWorld) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ createData o.slot item
    ⦃⇓? _ w => ⌜∃ delta, Handoff initial w [] [] delta⌝⦄ := by
  have eq : createData o.slot item = (do
      let some first := item.head? | invariant "an empty ring item"
      let ret ← createReturnSource o.slot item
      TxDisposition.createTailSource o.slot item first ret) := by
    simp only [TxDisposition.createSource_factor,createReturnSource,createPublishReturn,bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [eq]
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hi hr
  cases head : item.head? with
  | none => simp only [head] at hr; cases hr
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨ret,a,aa,hreturn,htail⟩ := hr
    have ha := (hoare_iff_run_ambient _ _ _).mp (createReturn_spec initial o item)
      w ambient ret a aa hi hreturn
    exact (hoare_iff_run_ambient _ _ _).mp (createTail_handoff initial o item first ret)
      a aa u v ambient' ha htail

/-- Exact acquisition, allocation and submission suffix of staged send. -/
theorem stagedSubmit_handoff (packets : List DataPacket) (hc : KeyCompatible pid kid w)
    (ambient ambient' : Ambient)
    (hr : ((do Affiliation.sendAcquire kid
               let item ← packets.mapM newTxSkb
               createData pid item).run w).run ambient = .ok (((),v),ambient')) :
    ∃ delta, Handoff w v [] [] delta := by
  obtain ⟨u,a,aa,ha,hr⟩ := bind_ok_native hr
  cases u
  obtain ⟨item,b,ab,hb,hcdata⟩ := bind_ok_native hr
  obtain ⟨d,p,hd,hp,pos,loan⟩ := sendAcquire_handoff hc ambient aa ha
  let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
  have hl : OpenLoan w o b := ⟨loan.after_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (newTxList_protect packets) a aa item b ab hb),
    by simpa [o,balance,resident,hd,hp] using pos⟩
  exact (hoare_iff_run_ambient _ _ _).mp (createData_handoff w o item)
    b ab () v ambient' hl hcdata

def Transfer (initial current : WGWorld) : Prop := ∃ delta, Handoff initial current [] [] delta

abbrev ProjectedTransfers {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGWorld) (a : StateT S m α) : Prop :=
  ProjectedAction project Transfer a

abbrev Transfers (a : WG.M α) : Prop := ProjectedTransfers id a
abbrev ProductTransfers (a : Leanux.M α) : Prop := ProjectedTransfers World.wg a

theorem Transfers.iff_run_ambient (a : WG.M α) :
    Transfers a ↔ ∀ w ambient x v ambient',
      (a.run w).run ambient = .ok ((x,v),ambient') → Transfer w v :=
  ProjectedAction.iff_run_ambient id Transfer a

theorem ProductTransfers.iff_run (a : Leanux.M α) :
    ProductTransfers a ↔ ∀ w x v, a.run w = .ok (x,v) → Transfer w.wg v.wg :=
  ProjectedAction.iff_run World.wg Transfer a

theorem Transfer.refl (w : WGWorld) : Transfer w w := ⟨{},Handoff.refl w⟩
theorem Transfer.trans (h : Transfer w u) (j : Transfer u v) : Transfer w v := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := j
  exact ⟨a.append b,ha.trans hb⟩
theorem Transfer.after_view (h : Transfer w u) (hv : protectView v = protectView u) : Transfer w v := by
  obtain ⟨d,h⟩ := h; exact ⟨d,h.after_view hv⟩
theorem transfer_stable (initial : WGWorld) : WGStoreStable (Transfer initial) := by
  intro w v hk h
  obtain ⟨d,h⟩ := h
  exact ⟨d,handoff_stable _ _ _ _ w v hk h⟩

/-- The callback may be an arbitrary action over the actual product state. -/
theorem Transfers.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : ProjectedTransfers project a) (initial : WGWorld) :
    ⦃fun w => ⌜Transfer initial (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜Transfer initial (project w)⌝⦄ :=
  ProjectedAction.wp h (Transfer initial) (fun _ _ step before => before.trans step)

theorem transfer_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun s => protectView (project s)) a) (initial : WGWorld) :
    ⦃fun w => ⌜Transfer initial (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜Transfer initial (project w)⌝⦄ := by
  apply hoare_consequence
    (h.wp (fun obs => ∃ w, Transfer initial w ∧ obs = protectView w))
  · intro w hi; exact ⟨project w,hi,rfl⟩
  · intro x v hi
    obtain ⟨w,h,he⟩ := hi
    exact h.after_view he

theorem installSend_handoff (o : Owner) :
    Handoff w {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]}}
      [o] [] {send := [o]} := by
  constructor
  · cases he : w.dev <;> simp [baseView,he]
  · cases he : w.dev <;> simp [rxView,he]
  · intro pid; cases he : w.dev <;> simp [handoffTxView,HandoffDelta.items,he,Function.comp_def]
  · cases he : w.dev <;> simp [sendView,he]
  · intro q
    have hb : peerView {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]}} = peerView w := by cases he : w.dev <;> simp [peerView,he]
    rw [balance_view hb]
    simp [HandoffDelta.owners]

def handshakeQueueTail (pid : PeerId) (pending : Bool) : WG.M Unit := do
  if ← branch .queuedAlreadyQueued (pending && !(← peekQueuedUnit .sendWorker pid)) then
    peerPut (some pid)
    return
  ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid (fun p => {p with handshakePending := true}))
  recordQueued .sendWorker pid
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}

theorem handshakeQueueTail_spec (initial : WGWorld) (o : Owner) (pending : Bool) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ handshakeQueueTail o.slot pending
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hi hr
  simp only [handshakeQueueTail,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨peek,a,aa,hpeek,queued,b,ab,hbranch,hr⟩ := hr
  have ha := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.peekQueuedUnit .sendWorker o.slot) (OpenLoan initial o))
    w ambient peek a aa hi hpeek
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (OpenLoan initial o) .queuedAlreadyQueued (pending && !peek))
    a aa queued b ab ha hbranch).2
  cases queued with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,c,ac,hput,hr⟩ := hr
    cases x
    cases hr
    exact ⟨{},repay_handoff hb.1 hb.2 ab _ hput⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,c,ac,hmodify,y,d,ad,hrecord,hr⟩ := hr
    have hc := (hoare_iff_run_ambient _ _ _).mp
      (open_frame (project := id)
        (modifyPeer_protect o.slot (fun p => {p with handshakePending := true}) (fun _ => rfl))
        initial o) b ab x c ac hb hmodify
    have hd := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.recordQueued .sendWorker o.slot) (OpenLoan initial o))
      c ac y d ad hc hrecord
    cases hr
    exact ⟨{send := [o]},by
      simpa [HandoffDelta.append] using hd.1.trans (installSend_handoff (w := d) o)⟩

def handshakeBorrow (pid : PeerId) (pending : Bool) : WG.M Unit := do
  peerGet pid
  handshakeQueueTail pid pending

theorem handshakeBorrow_transfers (pid : PeerId) (pending : Bool) : Transfers (handshakeBorrow pid pending) := by
  apply (Transfers.iff_run_ambient _).mpr
  intro w ambient x v ambient' hr
  obtain ⟨u,a,aa,hget,ht⟩ := bind_ok_native hr
  cases u
  obtain ⟨d,p,hd,hp,pos,h⟩ := peerGet_handoff ambient aa hget
  let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
  have hi : OpenLoan w o a := ⟨h,by simpa [o,balance,resident,hd,hp] using pos⟩
  exact (hoare_iff_run_ambient _ _ _).mp (handshakeQueueTail_spec w o pending)
    a aa x v ambient' hi ht

theorem modifyPeer_source (pid : PeerId) (f : Peer → Peer) :
    ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl

/-- The actual queue attempt peeks after acquisition, and records only the
send-work queue update. The obsolete factor also changed queuedThisCall. -/
def queuedSource (pid : PeerId) (retry : Bool) : WG.M Unit := do
  if ← branch .queuedNotRetry !retry then
    ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid (fun p => {p with timerHandshakeAttempts := 0}))
  let p ← getPeer pid
  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
  if ← branch .queuedDead p.isDead then return
  handshakeBorrow pid p.handshakePending

theorem queuedSource_eq (pid : PeerId) (retry : Bool) : queuedSource pid retry = sendQueuedHandshakeInitiation pid retry := by
  simp only [queuedSource,handshakeBorrow,handshakeQueueTail,sendQueuedHandshakeInitiation,
    modifyPeer_source,bind_assoc]

theorem sendQueued_transfers (pid : PeerId) (retry : Bool) : Transfers (sendQueuedHandshakeInitiation pid retry) := by
  apply (Transfers.iff_run_ambient _).mpr
  intro w ambient x v ambient' hr
  let tail : WG.M Unit := do
    let p ← getPeer pid
    if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
    if ← branch .queuedDead p.isDead then return
    handshakeBorrow pid p.handshakePending
  have ht : ⦃fun u => ⌜Transfer w u⌝⦄ tail ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro a aa u b ab hi run
    simp only [tail,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨p,c,ac,hget,expired,d,ad,hclock,run⟩ := run
    have hc : Transfer w c := by
      rw [(Peers.getPeer_current pid a c p aa ac hget).1]
      exact hi
    have hd := (hoare_iff_run_ambient _ _ _).mp
      (transfer_frame (project := id)
        ((branchExpired_sameWGWorld .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·)).factor protectView) w)
      c ac expired d ad hc hclock
    cases expired with
    | true =>
      simp only [ite_true] at run
      cases run
      exact hd
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dead,e,ae,hdead,run⟩ := run
      have he := ((hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (Transfer w) .queuedDead p.isDead)
        d ad dead e ae hd hdead).2
      cases dead with
      | true =>
        simp only [ite_true] at run
        cases run
        exact he
      | false =>
        simp only [Bool.false_eq_true,ite_false] at run
        exact (hoare_iff_run_ambient _ _ _).mp
          (Transfers.wp (handshakeBorrow_transfers pid p.handshakePending) w)
          e ae u b ab he run
  rw [← queuedSource_eq] at hr
  change ((do
    if ← branch .queuedNotRetry !retry then
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with timerHandshakeAttempts := 0}))
    tail).run w).run ambient = .ok ((x,v),ambient') at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨reset,a,aa,hbranch,hr⟩ := hr
  have ha := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (Transfer w) .queuedNotRetry !retry)
    w ambient reset a aa (Transfer.refl w) hbranch).2
  cases reset with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,b,ab,hmodify,hr⟩ := hr
    have hb := (hoare_iff_run_ambient _ _ _).mp
      (transfer_frame (project := id)
        (modifyPeer_protect pid (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => rfl)) w)
      a aa u b ab ha hmodify
    exact (hoare_iff_run_ambient _ _ _).mp ht b ab x v ambient' hb hr
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hr
    exact (hoare_iff_run_ambient _ _ _).mp ht a aa x v ambient' ha hr

end Leanux.Proofs.WG.Queues.RxCredits
