import Leanux.Proofs.WG.Queues.RxPollCarrier
import Leanux.Proofs.WG.Queues.RxRingEntry

/-! Actual admission transfers the index lookup's reference into the newly
allocated carrier. All statements concern the same supplied ledger and actual
normal source cuts; failed executions have no invented endpoint World. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

theorem setWord_keyRelation (s : Affiliation.State) (owner : IndexOwner) (word : Option PeerId)
    (hw : word = none ∨ s.word owner = some word) :
    KeyRelation NoPromotion (stateKeyView (some s))
      (stateKeyView (some (s.setWord owner word))) := by
  cases owner with
  | handshake id =>
    refine ⟨rfl,fun _ _ h => h,?_⟩
    intro pid stamp current hc
    refine ⟨current,?_,Or.inl rfl⟩
    by_cases he : pid=id
    · subst pid
      simpa [stateKeyView,Affiliation.State.setWord,Option.map_map,Function.comp_def] using hc
    · simpa [stateKeyView,Affiliation.State.setWord,he] using hc
  | keypair id =>
    refine ⟨rfl,?_,fun _ _ current h => ⟨current,h,Or.inl rfl⟩⟩
    intro kid pid hc
    by_cases he : kid=id
    · subst kid
      rcases hw with rfl | hw
      · simp [stateKeyView,Affiliation.State.setWord,Option.map_map,Function.comp_def] at hc
      · obtain ⟨old,hold,hword⟩ := Option.map_eq_some_iff.mp hw
        simp [stateKeyView,Affiliation.State.setWord,hold] at hc
        simpa [stateKeyView,hold,←hword] using hc
    · simpa [stateKeyView,Affiliation.State.setWord,he] using hc

/-- The unconditional acquisition facts, rather than valid-key material
retention, justify backward non-NULL words and unchanged current slots. -/
theorem acquisition_keyEffect (ha : Affiliation.Acquisition owner w result v ambient ambient') :
    KeyEffect NoPromotion w v := by
  have hf := ha.facts
  change KeyRelation NoPromotion (keyView w) (keyView v)
  rw [keyView_factor,keyView_factor,hf.2]
  cases hs : Affiliation.view w with
  | none => exact ⟨rfl,fun _ _ h => h,fun _ _ current h => ⟨current,h,Or.inl rfl⟩⟩
  | some s =>
    apply setWord_keyRelation s owner result
    simpa [Affiliation.wordAt,hs] using hf.1

theorem acquireOwner_keyEffect (owner : IndexOwner) :
    KeyEffects NoPromotion (Affiliation.acquireOwner owner) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient result v ambient' hr
  exact acquisition_keyEffect (Affiliation.acquireOwner_acquisition owner w v result ambient ambient' hr)

theorem indexLookup_keyEffect (kinds : List IndexKind) (index : Nat) :
    KeyEffects NoPromotion (indexLookup kinds index) := by
  apply keyEffects_of_wp
  intro initial
  let P := KeyEffect NoPromotion initial
  have hb (decision : Decision) (value : Bool) :
      Preserves P (branch decision value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have stop {α : Type} (why : String) : Preserves P (invariant why : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant why) P
  have hi : Preserves P (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    unfold P KeyEffect keyView keyWords currentCells at hg ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hg
  have ha := fun owner => KeyEffects.wp (acquireOwner_keyEffect owner) initial
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem loan_base (hl : Loan w result v) : baseView v=baseView w := by
  cases result with
  | none => exact base_of_peerView hl.1
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv,hx⟩ := hl
    rw [base_of_peerView hv]
    simp only [baseView,creditWorld,hd,Option.map_some,Option.bind_some]
    congr 1
    funext q
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem loan_rx (hl : Loan w result v) : rxView v=rxView w := by
  cases result with
  | none => exact hl.2
  | some pid => exact hl.choose_spec.choose_spec.2.2.2.2

/-- A concrete successful lookup retains all existing carriers and adds its
actual owner's reservation. The original positive count is source-derived. -/
theorem lookup_carriers (hi : CarrierState cs loans w) (ambient ambient' : Ambient)
    (hr : ((indexLookup kinds index).run w).run ambient=.ok ((some (owner,pid),v),ambient')) :
    ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧ 0<p.refcount ∧
      CarrierState cs (⟨d.ifindex,pid,p.internalId⟩::loans) v := by
  have hl := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan kinds index w)
    w ambient _ v ambient' rfl hr
  change Loan w (some pid) v at hl
  obtain ⟨d,p,hd,hp,pos,hfund⟩ := loan_protected hl hi.funded
  have hk := (KeyEffects.iff_run_ambient _ _).mp
    (indexLookup_keyEffect kinds index) w ambient _ v ambient' hr
  exact ⟨d,p,hd,hp,pos,inventory_view hi.inventory (loan_rx hl),
    queueOwners_base hi.queues (loan_base hl),hfund,
    hk.rxCompatible (loan_rx hl) hi.keys.1,
    hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩

theorem ownerStore_packets (owner : IndexOwner) (word : Option PeerId) :
    SameView Packets.snapshot (owner.setPeerWord word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases result
  cases owner with
  | handshake id =>
    unfold IndexOwner.setPeerWord at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨p,a,aa,hget,hset⟩ := hr
    obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal id w a p ambient aa hget
    cases hset
    simp [Packets.snapshot,Packets.deviceStore,hd]
  | keypair id =>
    obtain ⟨d,k,hd,hk,rfl,_⟩ := Origins.keypair_word_store id word w v ambient ambient' hr
    simp [Packets.snapshot,Packets.deviceStore,CounterWindow.store,hd]

theorem acquireOwner_packets (owner : IndexOwner) :
    SameView Packets.snapshot (Affiliation.acquireOwner owner) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  obtain ⟨word,a,b,aa,ab,hread,hget,hstore⟩ :=
    Affiliation.acquireOwner_acquisition owner w v result ambient ambient' hr
  have hk : a=w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun g => g=w)) w ambient word a aa rfl hread
  subst a
  have hb := (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.acquire_spec word (wgStoreView w))
    w aa result b ab rfl hget
  have hs := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ownerStore_packets owner result) b ab () v ambient' hstore
  rw [hs]
  cases result with
  | none =>
    have he : b.dev=w.dev := congrArg WGStoreView.dev hb.2
    simp only [Packets.snapshot,he]
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,he⟩ := hb.2
    have hedev := congrArg WGStoreView.dev he
    change b.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at hedev
    change w.dev=some d at hd
    simp [Packets.snapshot,Packets.deviceStore,hedev,hd]

theorem indexLookup_packets (kinds : List IndexKind) (index : Nat) :
    SameView Packets.snapshot (indexLookup kinds index) := by
  intro initial
  let P := fun g => Packets.snapshot g=initial
  have hb (decision : Decision) (value : Bool) :
      Preserves P (branch decision value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have stop {α : Type} (why : String) : Preserves P (invariant why : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant why) P
  have hi : Preserves P (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [P,Packets.snapshot,Packets.deviceStore,hd] using hg
  have ha := fun owner => (acquireOwner_packets owner).wp (fun t => t=initial)
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem receiveKey_packets (entry : Option (IndexOwner × PeerId)) :
    SameView Packets.snapshot (Affiliation.receiveKeyAcquire entry) := by
  have hk (kid) : SameView Packets.snapshot (keypairGet kid) := by
    intro initial
    let P := fun g => Packets.snapshot g=initial
    have getter (id) : Preserves P (getKeypair id) := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient k v ambient' hi hr
      simpa only [(KeyTimes.getKeypair_return id w v k ambient ambient' hr).1] using hi
    have setter (id) (k : Keypair) : Preserves P (setKeypair id k) := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient result v ambient' hi hr
      cases hr
      cases hd : w.dev <;> simpa [P,Packets.snapshot,Packets.deviceStore,modifyDev,hd] using hi
    unfold keypairGet
    material_lower
    repeat' first
      | unfold Preserves
      | material_join
      | material_join_use
      | (index_material_head refcountIncNotZero; unfold refcountIncNotZero; material_lower)
      | (index_material_head getKeypair; exact getter _)
      | (index_material_head setKeypair; exact setter _ _)
      | (index_material_head Pure.pure; exact preserves_pure _)
      | (index_material_head Bind.bind; apply preserves_bind)
      | material_component
      | material_intro
      | material_reduce
      | material_match
      | (index_material_head ite; split)
  cases entry with
  | none =>
    intro initial
    unfold Affiliation.receiveKeyAcquire keypairGetNull
    simp only [pure_bind,bind_assoc]
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairGetNull true) _)
    intro _
    exact preserves_pure _
  | some e =>
    rcases e with ⟨owner,pid⟩
    cases owner with
    | handshake id =>
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w ambient result v ambient' hr
      simp [Affiliation.receiveKeyAcquire,invariant,AmbientM.invariant] at hr
      cases hr
    | keypair id =>
      simpa [Affiliation.receiveKeyAcquire] using (hk (some id)).bind (fun _ => SameView.pure _ _)

theorem receiveKey_keyView (entry : Option (IndexOwner × PeerId)) :
    SameView keyView (Affiliation.receiveKeyAcquire entry) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient r v ambient' hr
  exact keyView_affiliation ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view w)) w ambient r v ambient' rfl hr).1

/-- The exact preallocation cut retains the supplied packet frontier, all old
carrier cells and their nullable key compatibility, and the actual lookup loan. -/
theorem admitted_front (hi : CarrierState cs loans w) (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((some ctx,v),ambient')) :
    ∃ before beforeAmbient o,
      ((newRxSkb ctx.packet).run before).run beforeAmbient=.ok ((ctx.slot,v),ambient') ∧
      CarrierState cs (o::loans) before ∧ o.slot=ctx.packet.peer ∧
      Packets.snapshot before=Packets.snapshot w := by
  obtain ⟨entry,a,aa,b,ab,c,ac,peer,d,ad,e,ae,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v ambient ambient' hr
  have ent := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a)) a aa _ b ab rfl hk).2 _ _ rfl
  obtain ⟨dev,p,hdev,hpeer,pos,ha⟩ := lookup_carriers hi ambient aa (ent ▸ hl)
  have fr := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (receiveKey_credit_frame entry) a aa _ b ab hk)
  have kb := (ProjectedAction.iff_run_ambient _ _ _).mp (receiveKey_keyView entry) a aa _ b ab hk
  have hb : CarrierState cs (⟨dev.ifindex,ctx.packet.peer,p.internalId⟩::loans) b :=
    ⟨inventory_view ha.inventory fr.2,queueOwners_view ha.queues fr.1,
      protected_view ha.funded fr.1,(keyEffect_of_view (allowed:=NoPromotion) kb).rxCompatible fr.2 ha.keys.1,currents_view kb ha.keys.2⟩
  have kc : c=b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair false) (fun g => g=b))
    b ab false c ac rfl hno
  have he : d=c := (getPeer_normal ctx.packet.peer c d peer ac ad hp).1
  have ke : e=d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g=d))
    d ad false e ae rfl hd
  refine ⟨e,ae,⟨dev.ifindex,ctx.packet.peer,p.internalId⟩,hn,?_,rfl,?_⟩
  · simpa only [ke,he,kc] using hb
  · have hs := ((ProjectedAction.iff_run_ambient _ _ _).mp
        (receiveKey_packets entry) a aa _ b ab hk).trans
        ((ProjectedAction.iff_run_ambient _ _ _).mp
        (indexLookup_packets [.keypair] (u32le msg 4)) w ambient entry a aa hl)
    simpa only [ke,he,kc] using hs

theorem allocate_rxCompatible (hi : RxCompatible w) (hk : KeyCompatible pkt.peer pkt.keypair w)
    (hd : w.dev=some d) :
    RxCompatible (Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1}) := by
  intro out id q hout hq target key htarget hkey
  have he : out={d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1} := by simpa [Packets.update,hd] using hout.symm
  have ht : target=out := Option.some.inj (htarget.symm.trans hout)
  subst target; subst out
  by_cases hn : d.nextSkb=id
  · have eq : q=pkt := by simpa [Std.TreeMap.getElem?_insert,hn] using hq.symm
    subst q
    exact hk d key hd hkey
  · exact hi d id q hd (by simpa [Std.TreeMap.getElem?_insert,hn] using hq) d key hd hkey

/-- The allocation result uses the actual frontier vacancy and consumes the
actual preallocation owner loan. No inventory is reselected at the endpoint. -/
theorem allocate_state {id : SkbId} (hi : CarrierState cs (o::loans) w) (hf : Packets.Inv w)
    (owner : o.slot=pkt.peer) (hk : KeyCompatible pkt.peer pkt.keypair w) (ambient ambient' : Ambient)
    (hr : ((newRxSkb pkt).run w).run ambient=.ok ((id,v),ambient')) :
    ∃ c, c.packet=⟨o.epoch,id⟩ ∧ c.owner=o ∧ c.phase=.unpublished ∧ CarrierState (c::cs) loans v := by
  have frame : Preserves (fun g => keyView g=keyView w) (newRxSkb pkt) := by
    unfold newRxSkb
    apply hoare_liftSkb
    intro g d store hg hd
    unfold keyView keyWords currentCells at hg ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hg
  have key := (hoare_iff_run_ambient _ _ _).mp frame w ambient id v ambient' rfl hr
  obtain ⟨dev,hd⟩ : ∃d,w.dev=some d := by
    cases hd : w.dev with
    | none => simp [newRxSkb,liftSkb_run,hd] at hr
    | some d => exact ⟨d,rfl⟩
  have fund := hi.funded o
  have positive : 0<balance w o := by simp [demand] at fund; omega
  obtain ⟨p,hp⟩ : ∃p,resident w o=some p := by
    cases h : resident w o with
    | none => simp [balance,h] at positive
    | some p => exact ⟨p,rfl⟩
  obtain ⟨d,hdev,epoch,hs,stamp⟩ := resident_fields hp
  have de : d=dev := Option.some.inj (hdev.symm.trans hd)
  subst d
  have fresh := (Packets.allocation_slots_empty w dev hd hf).2
  have out := allocate_inventory ambient hi.inventory hd fresh epoch.symm owner.symm
  rw [out.1] at hr
  cases hr
  refine ⟨_,by simp [epoch],rfl,rfl,out.2.1,?_,protected_view (loan_to_carrier hi.funded rfl) out.2.2,?_,?_⟩
  · intro d pid p id hd hp
    simpa [QueueOwners,List.filter_cons] using (queueOwners_view hi.queues out.2.2) d pid p id hd hp
  · exact allocate_rxCompatible hi.keys.1 hk hd
  · exact currents_view key hi.keys.2

/-- Successful original admission installs exactly its newly allocated carrier;
the existing packet invariant supplies vacancy at that actual allocation cut. -/
theorem admitted_state (hi : CarrierState cs loans w) (hf : Packets.Inv w) (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((some ctx,v),ambient')) :
    ∃ o, CarrierState (⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩::cs) loans v ∧
      o.slot=ctx.packet.peer ∧ KeyWord ctx.packet.keypair ctx.packet.peer v ∧
      RxOrigin.Admitted msg src ds ctx w v ambient ambient' := by
  obtain ⟨before,beforeAmbient,o,hn,hb,ho,hs⟩ := admitted_front hi ambient ambient' hr
  have word := admitted_key_word ambient ambient' hr
  have key : KeyCompatible ctx.packet.peer ctx.packet.keypair v := by
    obtain ⟨d,k,hd,hk,hword⟩ := word
    intro e q he hq
    have eq : e=d := Option.some.inj (he.symm.trans hd)
    subst e
    have eq : q=k := Option.some.inj (hq.symm.trans hk)
    subst q
    exact Or.inr hword
  have frame : Preserves (fun g => keyView g=keyView before) (newRxSkb ctx.packet) := by
    unfold newRxSkb
    apply hoare_liftSkb
    intro g d store hg hd
    unfold keyView keyWords currentCells at hg ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hg
  have he := (hoare_iff_run_ambient _ _ _).mp frame before beforeAmbient ctx.slot v ambient' rfl hn
  have oldkey := (keyEffect_of_view (allowed:=NoPromotion) he.symm).compatible key
  obtain ⟨c,hp,howner,hphase,hc⟩ := allocate_state hb (by simpa [Packets.Inv,hs] using hf) ho oldkey beforeAmbient ambient' hn
  have ce : c=⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ := by cases c; simp_all
  subst c
  exact ⟨o,hc,ho,word,RxOrigin.admission_execution _ _ _ _ _ _ ambient ambient' hr⟩

private theorem any_spec {S α : Type} (a : StateT S (Except Stop) α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro; intros; trivial

theorem receiveKey_peer (entry : Option (IndexOwner × PeerId)) (ambient ambient' : Ambient)
    (hr : ((Affiliation.receiveKeyAcquire entry).run w).run ambient=.ok (((kp,pid),v),ambient')) :
    pid=entry.map Prod.snd := by
  cases entry with
  | none =>
    simp [Affiliation.receiveKeyAcquire,keypairGetNull,branch,CounterWindow.branch_run,
      StateT.run_monadLift] at hr
    exact hr.1.1.2.symm
  | some e =>
    rcases e with ⟨owner,p⟩
    cases owner with
    | handshake id =>
      simp [Affiliation.receiveKeyAcquire,invariant,AmbientM.invariant] at hr
      cases hr
    | keypair id =>
      simp only [Affiliation.receiveKeyAcquire,pure_bind] at hr
      rw [MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨out,a,aa,hget,hret⟩ := hr
      change Except.ok (((out,some p),a),aa) = Except.ok (((kp,pid),v),ambient') at hret
      cases hret
      rfl

/-- Repayment consumes precisely the actual lookup loan. The initial positive
count makes this repayment nonfinal; no independent residency premise. -/
theorem loan_repay_state (hi : CarrierState cs loans w) (hl : Loan w pid u)
    (hk : KeyEffect NoPromotion w u) (ambient ambient' : Ambient)
    (hr : ((peerPut pid).run u).run ambient=.ok (((),v),ambient')) :
    CarrierState cs loans v := by
  cases pid with
  | none =>
    have he : v=u := by
      simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,
        StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
        CounterWindow.except_pure] at hr
      exact hr.1.symm
    subst v
    exact ⟨inventory_view hi.inventory hl.2,queueOwners_view hi.queues hl.1,
      protected_view hi.funded hl.1,hk.rxCompatible hl.2 hi.keys.1,
      hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hview,hrx⟩ := hl
    let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
    have b : balance u o= p.refcount+1 := by
      rw [balance_view hview,credit_balance hd hp]
      simp [o,balance,resident,hd,hp]
    obtain ⟨q,hq⟩ : ∃q,resident u o=some q := by
      cases h : resident u o with
      | none => simp [balance,h] at b
      | some q => exact ⟨q,rfl⟩
    obtain ⟨du,hdu,epoch,hpu,stamp⟩ := resident_fields hq
    have count : 1<q.refcount := by simpa [balance,hq] using (show 1<balance u o by omega)
    have paid := peerPut_handoff hdu hpu count ambient ambient' hr
    have hx := paid.rx.trans hrx
    have hb := paid.base.trans (loan_base (result:=some pid) ⟨d,p,hd,hp,pos,hview,hrx⟩)
    have he := hk.trans ((KeyEffects.iff_run_ambient _ _).mp
      (peerPut_keyEffect (some pid)) u ambient () v ambient' hr)
    refine ⟨inventory_view hi.inventory hx,queueOwners_base hi.queues hb,?_,
      he.rxCompatible hx hi.keys.1,he.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩
    intro owner
    rw [credit_repayment hd hp pos hview ambient ambient' hr owner]
    exact hi.funded owner

structure AdmissionFront (initial : WGWorld) (pid : Option PeerId) (w : WGWorld) : Prop where
  loan : Loan initial pid w
  keys : KeyEffect NoPromotion initial w

theorem AdmissionFront.kernel (h : AdmissionFront initial pid w)
    (hk : wgStoreView v=wgStoreView w) : AdmissionFront initial pid v := by
  have hd : v.dev=w.dev := congrArg WGStoreView.dev hk
  exact ⟨loan_after_frame h.loan (by unfold peerView; rw [hd]) (by unfold rxView; rw [hd]),
    h.keys.trans (keyEffect_of_view (by unfold keyView keyWords currentCells; rw [hd]))⟩

theorem AdmissionFront.keyPut (h : AdmissionFront initial pid w) (ambient ambient' : Ambient)
    (hr : ((keypairPut kp now).run w).run ambient=.ok (((),v),ambient')) : AdmissionFront initial pid v := by
  have hf := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame kp now) w ambient () v ambient' hr)
  exact ⟨loan_after_frame h.loan hf.1 hf.2,h.keys.trans
    ((KeyEffects.iff_run_ambient _ _).mp (keypairPut_keyEffect kp now) w ambient () v ambient' hr)⟩

theorem lookup_front (ambient aAmbient bAmbient : Ambient)
    (hr : ((indexLookup kinds index).run w).run ambient=.ok ((entry,a),aAmbient))
    (ha : ((Affiliation.receiveKeyAcquire entry).run a).run aAmbient=.ok (((kp,pid),b),bAmbient)) :
    AdmissionFront w pid b := by
  have hl := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan kinds index w)
    w ambient entry a aAmbient rfl hr
  have hp := receiveKey_peer entry aAmbient bAmbient ha
  have hf := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (receiveKey_credit_frame entry) a aAmbient _ b bAmbient ha)
  exact ⟨loan_after_frame (hp ▸ hl) hf.1 hf.2,
    ((KeyEffects.iff_run_ambient _ _).mp (indexLookup_keyEffect kinds index) w ambient entry a aAmbient hr).trans
      (keyEffect_of_view ((ProjectedAction.iff_run_ambient _ _ _).mp
        (receiveKey_keyView entry) a aAmbient _ b bAmbient ha))⟩

/-- The original no-key and dead-peer normal returns restore the supplied
carrier ledger by repaying the actual lookup reference. They need not roll
back key invalidation, owner store-back or recorded branches. -/
theorem admitted_none (hi : CarrierState cs loans w) (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((none,v),ambient')) :
    CarrierState cs loans v := by
  rw [RxOrigin.admitSource_factor] at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨entry,a,aa,hl,acquired,b,ab,hk,noKey,c,ac,hn,rest⟩ := hr
  rcases acquired with ⟨kp,pid⟩
  have front := lookup_front ambient aa ab hl hk
  have kc : c=b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair kp.isNone) (fun g => g=b))
    b ab noKey c ac rfl hn
  have fc : AdmissionFront w pid c := by simpa only [kc] using front
  cases noKey with
  | true =>
    simp only [↓reduceIte,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,z,az,hpay,he⟩ := rest
    cases u
    obtain ⟨⟨_,rfl⟩,rfl⟩ := he
    exact loan_repay_state hi fc.loan fc.keys ac _ hpay
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at rest
    cases kp with
    | none =>
      simp [invariant,AmbientM.invariant] at rest
      cases rest
    | some kid =>
      cases pid with
      | none =>
        simp [invariant,AmbientM.invariant] at rest
        cases rest
      | some pid =>
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨peer,d,ad,hread,dead,e,ae,hdead,rest⟩ := rest
        have kd : d=c := (getPeer_normal pid c d peer ac ad hread).1
        have ke : e=d := (hoare_iff_run_ambient _ _ _).mp
          (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g=d))
          d ad dead e ae rfl hdead
        have fe : AdmissionFront w (some pid) e := by simpa only [ke,kd] using fc
        cases dead with
        | true =>
          simp only [↓reduceIte,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨u,f,af,hkey,u,g,ag,hpay,he⟩ := rest
          cases u
          obtain ⟨⟨_,rfl⟩,rfl⟩ := he
          exact loan_repay_state hi (fe.keyPut ae af hkey).loan (fe.keyPut ae af hkey).keys af _ hpay
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨slot,z,az,ha,bad⟩ := rest
          simp at bad

end Leanux.Proofs.WG.Queues.RxCredits
