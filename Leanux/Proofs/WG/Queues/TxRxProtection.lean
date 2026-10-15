import Leanux.Proofs.WG.Queues.RxProtectionFrames

/-! Source-acquired temporary references and concrete TX publication. Every
normal endpoint theorem refers to the original call; Stops have no final World. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option pp.structureInstances false

theorem bind_ok {a : M α} {f : α → M β}
    (hr : (a >>= f).run w = .ok (y,v)) :
    ∃ x u, a.run w = .ok (x,u) ∧ (f x).run u = .ok (y,v) := by
  simp only [StateT.run_bind] at hr
  cases he : a.run w with
  | error e => simp [he] at hr
  | ok out => exact ⟨out.1,out.2,rfl,by simpa [he] using hr⟩

/-- Balanced borrowing around a concrete projection-preserving middle. This
lemma is instantiated below with the actual publication body, not a callback
that is assumed to preserve references. -/
theorem loan_middle_repay (pid : PeerId) (a : M Unit) (ha : SameView protectView a) :
    SameView protectView (do peerGet pid; a; peerPut (some pid)) := by
  intro w x v hr
  obtain ⟨_,u,hget,hr⟩ := bind_ok hr
  obtain ⟨_,b,hmid,hput⟩ := bind_ok hr
  obtain ⟨d,p,hd,hp,pos,h⟩ := peerGet_handoff hget
  have hc := h.after_view (ha u () b hmid)
  have old : 0 < balance w ⟨d.ifindex,pid,p.internalId⟩ := by simp [balance,resident,hd,hp,pos]
  have closed := repay_handoff hc old hput
  have hpv : peerView v = peerView w := by
    apply Prod.ext
    · simpa [peerView,baseView] using congrArg Prod.fst closed.base
    · funext q
      have hb := congrFun (congrArg Prod.snd closed.base) q
      cases hw : w.k.wg with
      | none =>
        have hv : v.k.wg = none := by
          have := congrArg Prod.fst closed.base
          simpa [baseView,hw] using this
        simp [peerView,hw,hv]
      | some dw =>
        cases hv : v.k.wg with
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

theorem publicationMiddle_protect (pid : PeerId) (first : SkbId) (state : PacketState) :
    SameView protectView (TxDisposition.publicationMiddle pid first state) := by
  apply SameView.of_wp
  intro s
  have hc := (cpu_protect pid).wp (fun t => t=s)
  have ht := (setTx_protect first (fun p => {p with state})).wp (fun t => t=s)
  have hp := (protect_kernel (peekQueuedUnit_sameKernel .txWorker pid)).wp (fun t => t=s)
  have hr := (protect_kernel (Lifetimes.recordQueued_sameKernel .txWorker pid)).wp (fun t => t=s)
  have hm := (modifyDev_protect (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [TxDisposition.publicationMiddle,hc,ht,hp,hr,hm,getPeer,getDev,getK,invariant]

theorem publication_protect (item : List SkbId) (state : PacketState) :
    SameView protectView (enqueuePerPeerTx item state) := by
  rw [TxDisposition.publication_factor]
  cases hh : item.head? with
  | none =>
    simp only [hh]
    intro w x v hr
    simp [invariant] at hr
  | some first =>
    simp only [hh]
    apply SameView.bind (getTx_protect first)
    intro pkt
    apply SameView.bind (protect_kernel (indexOwner_peerDeref_sameKernel (.keypair pkt.keypair)))
    intro pid
    exact loan_middle_repay pid _ (publicationMiddle_protect pid first state)

/-- The concrete per-peer TX queue installation transfers one already supplied
loan into one batch occurrence; packet identifiers need not be distinct. -/
theorem installTx_handoff (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (item : List SkbId) :
    Handoff w {w with k := {w.k with wg := some {d with peers := d.peers.insert pid {p with txQueue := p.txQueue.enqueue item}}}}
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
    have hv : peerView {w with k := {w.k with wg := some {d with peers := d.peers.insert pid {p with txQueue := p.txQueue.enqueue item}}}} = peerView w := by
      unfold peerView
      simp [hd,funext_iff,Std.TreeMap.getElem?_insert]
      intro q; by_cases he : pid=q <;> simp_all
    rw [balance_view hv]
    simp [HandoffDelta.owners]

/-- The exact original enqueue setter at its reached source cut. The input
record is obtained by the original getter, not by a stale arbitrary setter. -/
theorem installTx_source (pid : PeerId) (item : List SkbId) (w v : World)
    (hr : (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.enqueue item}).run w = .ok ((),v)) :
    ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p ∧
      Handoff w v [⟨d.ifindex,pid,p.internalId⟩] [] {tx := [⟨⟨d.ifindex,pid,p.internalId⟩,item⟩]} := by
  cases hd : w.k.wg with
  | none => simp [getPeer,getDev,getK,hd,invariant] at hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [getPeer,getDev,getK,hd,hp,invariant] at hr
    | some p =>
      simp [getPeer,getDev,getK,hd,hp,setPeer,modifyDev,modifyK] at hr
      subst v
      exact ⟨d,p,rfl,hp,installTx_handoff hd hp item⟩

/-- The actual staged acquisition fixes its caller from the resident nullable
word. NULL and missing owners retain their original Stops. -/
theorem sendAcquire_handoff (hc : KeyCompatible pid kid w)
    (hr : (Affiliation.sendAcquire kid).run w = .ok ((),v)) :
    ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Handoff w v [] [⟨d.ifindex,pid,p.internalId⟩] {} := by
  obtain ⟨d,k,actual,p,hd,hk,hw,hp,pos,hb⟩ := Affiliation.sendAcquire_certificate kid w v hr
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
  simp [creditKernel,hv]

/-- Actual list allocation retains the already acquired loan; the packet list
and its output slot list are those of the original mapM, without extra getters. -/
theorem newTxList_protect (packets : List DataPacket) :
    SameView protectView (packets.mapM newTxSkb) := by
  induction packets with
  | nil => simpa using SameView.pure protectView ([] : List SkbId)
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact (newTx_protect p).bind fun _ => ih.bind fun _ => SameView.pure _ _

def OpenLoan (initial : World) (o : Owner) (current : World) : Prop :=
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

theorem open_frame (ha : SameView protectView a) (initial : World) (o : Owner) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ a ⦃⇓? _ w => ⌜OpenLoan initial o w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact ⟨h.1.after_view (ha w x v hr),h.2⟩

theorem open_getPeer (initial : World) (o : Owner) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ getPeer o.slot
    ⦃⇓? p w => ⌜OpenLoan initial o w ∧ resident w o = some p⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w p v h hr
  obtain ⟨old,hold,pos⟩ := h.resident
  obtain ⟨d,hd,he,hp,ht⟩ := resident_fields hold
  simp [getPeer,getDev,getK,hd,hp] at hr
  obtain ⟨rfl,rfl⟩ := hr
  exact ⟨h,hold⟩

theorem open_install (initial : World) (o : Owner) (p : Peer) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w ∧ resident w o = some p⌝⦄
      setPeer o.slot {p with txQueue := p.txQueue.enqueue item}
    ⦃⇓? _ w => ⌜Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  obtain ⟨d,hd,he,hp,ht⟩ := resident_fields h.2
  have ho : o = ⟨d.ifindex,o.slot,p.internalId⟩ := by cases o; simp_all
  have hi := installTx_handoff (w:=w) hd hp item
  rw [← ho] at hi
  cases hr
  have hi' : Handoff w (w |> fun v => {v with k := {v.k with wg := v.k.wg.map fun d => {d with peers := d.peers.insert o.slot {p with txQueue := p.txQueue.enqueue item}}}}) [o] [] {tx := [⟨o,item⟩]} := by
    simpa [hd] using hi
  simpa [HandoffDelta.append,setPeer,modifyDev,modifyK] using h.1.1.trans hi'

theorem freeTxList_protect (item : List SkbId) : SameView protectView (TxDisposition.freeList item) := by
  induction item with
  | nil => simpa [TxDisposition.freeList_nil] using SameView.pure protectView ()
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact (freeTx_protect id).bind fun _ => ih

/-- The original createData cleanup consumes its previously acquired loan.
Its key put can Stop; the contract makes no claim about a failed endpoint. -/
theorem createCleanup_handoff (h : OpenLoan initial o w)
    (hr : (TxDisposition.cleanupSource o.slot item first).run w = .ok ((),v)) :
    Handoff initial v [] [] {} := by
  unfold TxDisposition.cleanupSource at hr
  obtain ⟨pkt,a,hget,hr⟩ := bind_ok hr
  obtain ⟨_,b,hkey,hr⟩ := bind_ok hr
  obtain ⟨_,c,hpeer,hfree⟩ := bind_ok hr
  have hb := (h.1.after_view (getTx_protect first w pkt a hget)).after_view
    (keypairPut_protect (some pkt.keypair) false a () b hkey)
  have hc := repay_handoff hb h.2 hpeer
  exact hc.after_view (freeTxList_protect item c () v hfree)

/-- The original post-installation enqueue continuation, including ring installation. -/
def enqueueTailItem (item : List SkbId) : M Int := do
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
  simp only [enqueuePerDeviceAndPeer,enqueueTailItem,bind_assoc,pure_bind]
  rfl

theorem enqueueTailItem_spec (initial : World) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ enqueueTailItem item
    ⦃⇓? ret w => ⌜(ret = 0 ∨ ret = -EPIPE) ∧ Handoff initial w [] [] {tx := [⟨o,item⟩]}⌝⦄ := by
  have hc := fun cpu => handoff_frame_spec (protect_kernel (Lifetimes.cpumaskNextOnlineFrom_sameKernel cpu)) initial [] [] {tx := [⟨o,item⟩]}
  have hq := handoff_frame_spec (protect_kernel (Lifetimes.queueDeviceWork_sameKernel .encryptWorker)) initial [] [] {tx := [⟨o,item⟩]}
  have hm := fun cpu => handoff_frame_spec (modifyDev_protect (fun d => {d with encryptLastCpu := cpu})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) initial [] [] {tx := [⟨o,item⟩]}
  have hp := handoff_frame_spec (modifyDev_protect (fun d => {d with encryptQueue := d.encryptQueue.produce item})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) initial [] [] {tx := [⟨o,item⟩]}
  mvcgen [enqueueTailItem,hc,hq,hm,hp,getDev,getK,branch,invariant]
  case vc3.h_1.post.success.post.success.isTrue =>
    rename_i w h t hb
    exact ⟨Or.inr (by trivial),h.after_view rfl⟩
  all_goals first
    | (rename_i h _ hb; exact h.after_view rfl)
    | (rename_i h; exact ⟨Or.inl rfl,h⟩)

theorem enqueue_open (initial : World) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ enqueuePerDeviceAndPeer o.slot item
    ⦃⇓? ret w => ⌜(ret = -ENOSPC ∧ OpenLoan initial o w) ∨
      ((ret = 0 ∨ ret = -EPIPE) ∧ Handoff initial w [] [] {tx := [⟨o,item⟩]})⌝⦄ := by
  rw [enqueue_factor]
  have ht := fun first => open_frame (setTx_protect first (fun p => {p with state := .uncrypted})) initial o
  have hg := open_getPeer initial o
  have hs := fun p => open_install initial o p item
  have tail := enqueueTailItem_spec initial o item
  mvcgen [ht,hg,hs,tail,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals first
    | (intro h hc; exact Or.inr ⟨h,hc⟩)
    | (rename_i old _ full; exact Or.inl ⟨by trivial,old.1.1.after_view rfl,old.1.2⟩)
    | (rename_i old _ full; exact ⟨⟨old.1.1.after_view rfl,old.1.2⟩,old.2⟩)

def KernelStable (P : World → Prop) : Prop := ∀ w v, v.k = w.k → P w → P v

theorem handoff_stable (initial : World) (before after : Reservations) (d : HandoffDelta) :
    KernelStable (fun w => Handoff initial w before after d) := by
  intro w v hk h
  apply h.after_view
  unfold protectView peerView rxView handoffTxView sendView
  rw [hk]

theorem open_stable (initial : World) (o : Owner) : KernelStable (OpenLoan initial o) := by
  intro w v hk h
  exact ⟨handoff_stable initial [] [o] {} w v hk h.1,h.2⟩

theorem branch_predicate (P : World → Prop) (hp : KernelStable P) (decision : Decision) (value : Bool) :
    ⦃fun w => ⌜P w⌝⦄ branch decision value ⦃⇓? result w => ⌜result = value ∧ P w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v h hr
  rw [Leanux.Proofs.WG.CounterWindow.branch_run] at hr
  cases hr
  exact ⟨rfl,hp w _ rfl h⟩

def CreateRet (initial : World) (o : Owner) (item : List SkbId) (ret : Int) (w : World) : Prop :=
  if ret = 0 ∨ ret = -EPIPE then Handoff initial w [] [] {tx := [⟨o,item⟩]}
  else OpenLoan initial o w

theorem createRet_stable (initial : World) (o : Owner) (item : List SkbId) (ret : Int) :
    KernelStable (CreateRet initial o item ret) := by
  unfold CreateRet
  split
  · exact handoff_stable _ _ _ _
  · exact open_stable _ _

theorem createTail_handoff (initial : World) (o : Owner) (item : List SkbId) (first : SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret w⌝⦄ TxDisposition.createTailSource o.slot item first ret
    ⦃⇓? _ w => ⌜∃ delta, Handoff initial w [] [] delta⌝⦄ := by
  have hb := branch_predicate (CreateRet initial o item ret) (createRet_stable initial o item ret)
  have hc : ⦃fun w => ⌜OpenLoan initial o w⌝⦄ TxDisposition.cleanupSource o.slot item first
      ⦃⇓? _ w => ⌜∃ delta, Handoff initial w [] [] delta⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w x v h hr
    exact ⟨{},createCleanup_handoff h hr⟩
  mvcgen [TxDisposition.createTailSource,hb,hc]
  all_goals simp_all [CreateRet,WG.EPIPE,EPIPE]
  all_goals grind

theorem createRet_frame (ha : SameView protectView a) (initial : World) (o : Owner)
    (item : List SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret w⌝⦄ a
    ⦃⇓? _ w => ⌜CreateRet initial o item ret w⌝⦄ := by
  unfold CreateRet
  split
  · exact handoff_frame_spec ha _ _ _ _
  · exact open_frame ha _ _

def createPublishReturn (item : List SkbId) (ret : Int) : M Int := do
  if ← branch .createDataEpipe (ret == -WG.EPIPE) then enqueuePerPeerTx item .dead
  return ret

theorem createPublishReturn_spec (initial : World) (o : Owner) (item : List SkbId) (ret : Int) :
    ⦃fun w => ⌜CreateRet initial o item ret w⌝⦄ createPublishReturn item ret
    ⦃⇓? result w => ⌜result = ret ∧ CreateRet initial o item ret w⌝⦄ := by
  have hb := branch_predicate (CreateRet initial o item ret) (createRet_stable initial o item ret)
  have hp := createRet_frame (publication_protect item .dead) initial o item ret
  mvcgen [createPublishReturn,hb,hp]
  all_goals simp_all

def createReturnSource (pid : PeerId) (item : List SkbId) : M Int := do
  if ← branch .createDataDead (← getPeer pid).isDead then return -EINVAL
  let ret ← enqueuePerDeviceAndPeer pid item
  createPublishReturn item ret

theorem createReturn_spec (initial : World) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ createReturnSource o.slot item
    ⦃⇓? ret w => ⌜CreateRet initial o item ret w⌝⦄ := by
  have hg := open_getPeer initial o
  have hb := branch_predicate (OpenLoan initial o) (open_stable initial o)
  have he := enqueue_open initial o item
  have hp := createPublishReturn_spec initial o item
  mvcgen [createReturnSource,hg,hb,he,hp]
  all_goals simp_all [CreateRet,WG.EPIPE,EPIPE,ENOSPC,EINVAL]
  all_goals grind

theorem bind_if_source (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
    (if c then a else b) >>= f = (if c then a >>= f else b >>= f) := by
  split <;> rfl

/-- Full original createData after its actual matched acquisition. -/
theorem createData_handoff (initial : World) (o : Owner) (item : List SkbId) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ createData o.slot item
    ⦃⇓? _ w => ⌜∃ delta, Handoff initial w [] [] delta⌝⦄ := by
  have eq : createData o.slot item = (do
      let some first := item.head? | invariant "an empty ring item"
      let ret ← createReturnSource o.slot item
      TxDisposition.createTailSource o.slot item first ret) := by
    simp only [TxDisposition.createSource_factor,createReturnSource,createPublishReturn,bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [eq]
  have hr := createReturn_spec initial o item
  have ht := createTail_handoff initial o item
  mvcgen [hr,ht,invariant]

/-- Exact acquisition, allocation and submission suffix of staged send. -/
theorem stagedSubmit_handoff (packets : List DataPacket) (hc : KeyCompatible pid kid w)
    (hr : (do Affiliation.sendAcquire kid
              let item ← packets.mapM newTxSkb
              createData pid item).run w = .ok ((),v)) :
    ∃ delta, Handoff w v [] [] delta := by
  obtain ⟨_,a,ha,hr⟩ := bind_ok hr
  obtain ⟨item,b,hb,hcdata⟩ := bind_ok hr
  obtain ⟨d,p,hd,hp,pos,loan⟩ := sendAcquire_handoff hc ha
  let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
  have hl : OpenLoan w o b := ⟨loan.after_view (newTxList_protect packets a item b hb),
    by simpa [o,balance,resident,hd,hp] using pos⟩
  exact (hoare_iff_triple _ _ _).mpr (createData_handoff w o item) b () v hl hcdata

def Transfer (initial current : World) : Prop := ∃ delta, Handoff initial current [] [] delta

def Transfers (a : M α) : Prop := ∀ w x v, a.run w = .ok (x,v) → Transfer w v

theorem Transfer.refl (w : World) : Transfer w w := ⟨{},Handoff.refl w⟩
theorem Transfer.trans (h : Transfer w u) (j : Transfer u v) : Transfer w v := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := j
  exact ⟨a.append b,ha.trans hb⟩
theorem Transfer.after_view (h : Transfer w u) (hv : protectView v = protectView u) : Transfer w v := by
  obtain ⟨d,h⟩ := h; exact ⟨d,h.after_view hv⟩
theorem transfer_stable (initial : World) : KernelStable (Transfer initial) := by
  intro w v hk h
  obtain ⟨d,h⟩ := h
  exact ⟨d,handoff_stable _ _ _ _ w v hk h⟩
theorem Transfers.wp (h : Transfers a) (initial : World) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ a ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  exact hi.trans (h w x v hr)
theorem transfer_frame (h : SameView protectView a) (initial : World) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ a ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  exact fun _ _ _ hi hr => hi.after_view (h _ _ _ hr)

theorem installSend_handoff (o : Owner) :
    Handoff w {w with k := {w.k with wg := w.k.wg.map fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]}}}
      [o] [] {send := [o]} := by
  constructor
  · cases he : w.k.wg <;> simp [baseView,he]
  · cases he : w.k.wg <;> simp [rxView,he]
  · intro pid; cases he : w.k.wg <;> simp [handoffTxView,HandoffDelta.items,he,Function.comp_def]
  · cases he : w.k.wg <;> simp [sendView,he]
  · intro q
    have hb : peerView {w with k := {w.k with wg := w.k.wg.map fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]}}} = peerView w := by cases he : w.k.wg <;> simp [peerView,he]
    rw [balance_view hb]
    simp [HandoffDelta.owners]

def handshakeQueueTail (pid : PeerId) (pending : Bool) : M Unit := do
  if ← branch .queuedAlreadyQueued pending then
    peerPut (some pid)
    return
  ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid (fun p => {p with handshakePending := true}))
  recordQueued .sendWorker pid
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
  modify fun w => {w with queuedThisCall := pid :: w.queuedThisCall}

theorem handshakeQueueTail_spec (initial : World) (o : Owner) (pending : Bool) :
    ⦃fun w => ⌜OpenLoan initial o w⌝⦄ handshakeQueueTail o.slot pending
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  have hb := branch_predicate (OpenLoan initial o) (open_stable initial o)
  have hp : ⦃fun w => ⌜OpenLoan initial o w⌝⦄ peerPut (some o.slot)
      ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    exact fun _ _ _ h hr => ⟨{},repay_handoff h.1 h.2 hr⟩
  have hm := open_frame (modifyPeer_protect o.slot (fun p => {p with handshakePending := true}) (fun _ => rfl)) initial o
  have hr := open_frame (protect_kernel (Lifetimes.recordQueued_sameKernel .sendWorker o.slot)) initial o
  have hs : ⦃fun w => ⌜OpenLoan initial o w⌝⦄
      modifyDev (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]})
      ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w x v h run
    cases run
    exact ⟨{send := [o]},by simpa [modifyDev,modifyK,HandoffDelta.append] using h.1.trans (installSend_handoff (w:=w) o)⟩
  change ⦃fun w => ⌜OpenLoan initial o w⌝⦄ (do
    if ← branch .queuedAlreadyQueued pending then peerPut (some o.slot); return
    ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) o.slot (fun p => {p with handshakePending := true}))
    recordQueued .sendWorker o.slot
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [o.slot]}
    modify fun (w : World) => {w with queuedThisCall := o.slot :: w.queuedThisCall})
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄
  mvcgen [hb,hp,hm,hr,hs]
  all_goals try simp_all
  all_goals rename_i h
  all_goals exact h.after_view rfl

def handshakeBorrow (pid : PeerId) (pending : Bool) : M Unit := do
  peerGet pid
  handshakeQueueTail pid pending

theorem handshakeBorrow_transfers (pid : PeerId) (pending : Bool) : Transfers (handshakeBorrow pid pending) := by
  intro w x v hr
  obtain ⟨_,u,hget,ht⟩ := bind_ok hr
  obtain ⟨d,p,hd,hp,pos,h⟩ := peerGet_handoff hget
  let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
  have hi : OpenLoan w o u := ⟨h,by simpa [o,balance,resident,hd,hp] using pos⟩
  exact (hoare_iff_triple _ _ _).mpr (handshakeQueueTail_spec w o pending) u x v hi ht

theorem modifyPeer_source (pid : PeerId) (f : Peer → Peer) :
    ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl

def queuedSource (pid : PeerId) (retry : Bool) : M Unit := do
  requireNotPending pid "queueing a handshake"
  if ← branch .queuedNotRetry !retry then
    ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid (fun p => {p with timerHandshakeAttempts := 0}))
  let p ← getPeer pid
  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
  if ← branch .queuedDead p.isDead then return
  handshakeBorrow pid p.handshakePending

theorem queuedSource_eq (pid : PeerId) (retry : Bool) : queuedSource pid retry = sendQueuedHandshakeInitiation pid retry := by
  simp only [queuedSource,handshakeBorrow,handshakeQueueTail,sendQueuedHandshakeInitiation,
    modifyPeer_source,bind_assoc,pure_bind]

theorem sendQueued_transfers (pid : PeerId) (retry : Bool) : Transfers (sendQueuedHandshakeInitiation pid retry) := by
  intro w x v hr
  have spec : ⦃fun u => ⌜Transfer w u⌝⦄ queuedSource pid retry ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    have hb := branch_predicate (Transfer w) (transfer_stable w)
    have hm := transfer_frame (modifyPeer_protect pid (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => rfl)) w
    have ht := fun date => transfer_frame (protect_kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))) w
    have hs := fun pending => (handshakeBorrow_transfers pid pending).wp w
    mvcgen [queuedSource,hb,hm,ht,hs,requireNotPending,getPeer,getDev,getK,invariant]
    all_goals simp_all
  rw [← queuedSource_eq] at hr
  exact (hoare_iff_triple _ _ _).mpr spec w x v (Transfer.refl w) hr

end Leanux.Proofs.WG.Queues.RxCredits
