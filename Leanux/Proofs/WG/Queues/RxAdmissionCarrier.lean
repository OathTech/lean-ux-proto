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
theorem acquisition_keyEffect (ha : Affiliation.Acquisition owner w result v) :
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
    KeyEffects NoPromotion (Affiliation.acquireOwner owner) :=
  fun w result v hr => acquisition_keyEffect (Affiliation.acquireOwner_acquisition owner w v result hr)

theorem indexLookup_keyEffect (kinds : List IndexKind) (index : Nat) :
    KeyEffects NoPromotion (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  apply keyEffects_of_wp
  intro initial
  have hb := fun decision value => (keyEffects_view (allowed:=NoPromotion)
    (keyView_kernel (sameKernel_branch decision value))).wp initial
  have hi := (keyEffects_view (allowed:=NoPromotion)
    (keyView_kernel (Framing.indexBucket_sameKernel index))).wp initial
  have ha := fun owner => (acquireOwner_keyEffect owner).wp initial
  mvcgen [Affiliation.indexLookupSource,hb,hi,ha,invariant]
  all_goals try exact ((⇓? _ w => ⌜KeyEffect NoPromotion initial w⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all

theorem loan_base (hl : Loan w result v) : baseView v=baseView w := by
  cases result with
  | none => exact base_of_peerView hl.1
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,hv,hx⟩ := hl
    rw [base_of_peerView hv]
    simp only [baseView,creditKernel,hd,Option.map_some,Option.bind_some]
    congr 1
    funext q
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem loan_rx (hl : Loan w result v) : rxView v=rxView w := by
  cases result with
  | none => exact hl.2
  | some pid => exact hl.choose_spec.choose_spec.2.2.2.2

/-- A concrete successful lookup retains all existing carriers and adds its
actual owner's reservation. The original positive count is source-derived. -/
theorem lookup_carriers (hi : CarrierState cs loans w)
    (hr : (indexLookup kinds index).run w=.ok (some (owner,pid),v)) :
    ∃ d p, w.k.wg=some d ∧ d.peers[pid]?=some p ∧ 0<p.refcount ∧
      CarrierState cs (⟨d.ifindex,pid,p.internalId⟩::loans) v := by
  have hl := (hoare_iff_triple _ _ _).mpr (indexLookup_loan kinds index w) w _ v rfl hr
  change Loan w (some pid) v at hl
  obtain ⟨d,p,hd,hp,pos,hfund⟩ := loan_protected hl hi.funded
  have hk := indexLookup_keyEffect kinds index w _ v hr
  exact ⟨d,p,hd,hp,pos,inventory_view hi.inventory (loan_rx hl),
    queueOwners_base hi.queues (loan_base hl),hfund,
    hk.rxCompatible (loan_rx hl) hi.keys.1,
    hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩


theorem ownerStore_packets (owner : IndexOwner) (word : Option PeerId) :
    SameView Packets.snapshot (owner.setPeerWord word) := by
  apply SameView.of_wp
  intro s
  cases owner <;> mvcgen [IndexOwner.setPeerWord,getPeer,getKeypair,getDev,getK,setPeer,setKeypair,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Packets.snapshot,Packets.deviceStore]

theorem acquireOwner_packets (owner : IndexOwner) :
    SameView Packets.snapshot (Affiliation.acquireOwner owner) := by
  intro w result v hr
  obtain ⟨word,a,b,hread,hget,hstore⟩ := Affiliation.acquireOwner_acquisition owner w v result hr
  have hk := indexOwner_peerWord_sameKernel owner w word a hread
  have hb := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec word a.k) a result b rfl hget
  have hs := ownerStore_packets owner result b () v hstore
  rw [hs]
  cases result with
  | none =>
    have he : b.k=w.k := hb.2.trans hk
    simp [Packets.snapshot,he]
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,he⟩ := hb.2
    simp [Packets.snapshot,Packets.deviceStore,he,←hk,hd]

theorem indexLookup_packets (kinds : List IndexKind) (index : Nat) :
    SameView Packets.snapshot (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  apply SameView.of_wp
  intro s
  have ha := fun owner => (acquireOwner_packets owner).wp (fun t => t=s)
  mvcgen [Affiliation.indexLookupSource,ha,indexBucket,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜Packets.snapshot w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Packets.snapshot]

theorem receiveKey_packets (entry : Option (IndexOwner × PeerId)) :
    SameView Packets.snapshot (Affiliation.receiveKeyAcquire entry) := by
  have hk (kid) : SameView Packets.snapshot (keypairGet kid) := by
    apply SameView.of_wp
    intro s
    mvcgen [keypairGet,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
      refcountIncNotZero,branchCmp,branchCmpExcluded,branch,invariant,unsupported]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [Packets.snapshot,Packets.deviceStore]
  cases entry with
  | none =>
    apply SameView.of_wp
    intro s
    have hn := sameKernel_wp _ Lifetimes.keypairGetCurrent_sameKernel
      (fun k => (match k.wg with | none => ⟨0,fun _ => none⟩ | some d => Packets.deviceStore d)=s)
    mvcgen [Affiliation.receiveKeyAcquire,hn]
  | some e =>
    rcases e with ⟨owner,pid⟩
    cases owner
    · apply SameView.of_wp
      intro s
      mvcgen [Affiliation.receiveKeyAcquire,invariant]
    · simpa [Affiliation.receiveKeyAcquire] using (hk (some _)).bind (fun _ => SameView.pure _ _)

theorem receiveKey_keyView (entry : Option (IndexOwner × PeerId)) :
    SameView keyView (Affiliation.receiveKeyAcquire entry) := by
  intro w r v hr
  exact keyView_affiliation ((hoare_iff_triple _ _ _).mpr
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view w)) w r v rfl hr).1

/-- The exact preallocation cut retains the supplied packet frontier, all old
carrier cells and their nullable key compatibility, and the actual lookup loan. -/
theorem admitted_front (hi : CarrierState cs loans w)
    (hr : (RxOrigin.admitSource msg src ds).run w=.ok (some ctx,v)) :
    ∃ before o, (newRxSkb ctx.packet).run before=.ok (ctx.slot,v) ∧
      CarrierState cs (o::loans) before ∧ o.slot=ctx.packet.peer ∧
      Packets.snapshot before=Packets.snapshot w := by
  obtain ⟨entry,a,b,c,peer,d,e,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v hr
  have ent := ((hoare_iff_triple _ _ _).mpr
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a)) a _ b rfl hk).2 _ _ rfl
  obtain ⟨dev,p,hdev,hpeer,pos,ha⟩ := lookup_carriers hi (ent ▸ hl)
  have fr := Prod.mk.inj (receiveKey_credit_frame entry a _ b hk)
  have kb := receiveKey_keyView entry a _ b hk
  have hb : CarrierState cs (⟨dev.ifindex,ctx.packet.peer,p.internalId⟩::loans) b :=
    ⟨inventory_view ha.inventory fr.2,queueOwners_view ha.queues fr.1,
      protected_view ha.funded fr.1,(keyEffect_of_view (allowed:=NoPromotion) kb).rxCompatible fr.2 ha.keys.1,currents_view kb ha.keys.2⟩
  have kc := sameKernel_branch .dataNoKeypair false b false c hno
  obtain ⟨he,_,_,_⟩ := getPeer_normal ctx.packet.peer c d peer hp
  have ke := sameKernel_branch .dataPeerDead peer.isDead d false e hd
  refine ⟨e,_,hn,(hb.kernel kc).kernel (ke.trans (congrArg World.k he)),rfl,?_⟩
  have hs := (receiveKey_packets entry a _ b hk).trans (indexLookup_packets [.keypair] (u32le msg 4) w entry a hl)
  simpa [Packets.snapshot,ke,he,kc] using hs

theorem allocate_keyView (pkt : RxPacket) : SameView keyView (newRxSkb pkt) := by
  apply SameView.of_wp
  intro s
  mvcgen [newRxSkb,getDev,getK,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold keyView keyWords currentCells at *
  all_goals simp_all

theorem allocate_rxCompatible (hi : RxCompatible w) (hk : KeyCompatible pkt.peer pkt.keypair w)
    (hd : w.k.wg=some d) :
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
    (owner : o.slot=pkt.peer) (hk : KeyCompatible pkt.peer pkt.keypair w)
    (hr : (newRxSkb pkt).run w=.ok (id,v)) :
    ∃ c, c.packet=⟨o.epoch,id⟩ ∧ c.owner=o ∧ c.phase=.unpublished ∧ CarrierState (c::cs) loans v := by
  obtain ⟨dev,hd⟩ : ∃d,w.k.wg=some d := by
    cases hd : w.k.wg with
    | none => simp [newRxSkb,getDev,getK,hd,invariant] at hr
    | some d => exact ⟨d,rfl⟩
  have fund := hi.funded o
  have positive : 0<balance w o := by simp [demand,List.count_cons] at fund; omega
  obtain ⟨p,hp⟩ : ∃p,resident w o=some p := by
    cases h : resident w o with
    | none => simp [balance,h] at positive
    | some p => exact ⟨p,rfl⟩
  obtain ⟨d,hdev,epoch,hs,stamp⟩ := resident_fields hp
  have de : d=dev := Option.some.inj (hdev.symm.trans hd)
  subst d
  have fresh := (Packets.allocation_slots_empty w dev hd hf).2
  have out := allocate_inventory hi.inventory hd fresh epoch.symm owner.symm
  rw [out.1] at hr
  cases hr
  refine ⟨_,by simp [epoch],rfl,rfl,out.2.1,?_,protected_view (loan_to_carrier hi.funded rfl) out.2.2,?_,?_⟩
  · intro d pid p id hd hp
    simpa [QueueOwners,List.filter_cons] using (queueOwners_view hi.queues out.2.2) d pid p id hd hp
  · exact allocate_rxCompatible hi.keys.1 hk hd
  · exact currents_view (allocate_keyView pkt _ _ _ out.1) hi.keys.2


/-- Successful original admission installs exactly its newly allocated carrier;
the existing packet invariant supplies vacancy at that actual allocation cut. -/
theorem admitted_state (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (hr : (RxOrigin.admitSource msg src ds).run w=.ok (some ctx,v)) :
    ∃ o, CarrierState (⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩::cs) loans v ∧
      o.slot=ctx.packet.peer ∧ KeyWord ctx.packet.keypair ctx.packet.peer v ∧
      RxOrigin.Admitted msg src ds ctx w v := by
  obtain ⟨before,o,hn,hb,ho,hs⟩ := admitted_front hi hr
  have word := admitted_key_word hr
  have key : KeyCompatible ctx.packet.peer ctx.packet.keypair v := by
    obtain ⟨d,k,hd,hk,hword⟩ := word
    intro e q he hq
    have eq : e=d := Option.some.inj (he.symm.trans hd)
    subst e
    have eq : q=k := Option.some.inj (hq.symm.trans hk)
    subst q
    exact Or.inr hword
  have oldkey := (keyEffect_of_view (allowed:=NoPromotion) (allocate_keyView ctx.packet before _ v hn).symm).compatible key
  obtain ⟨c,hp,howner,hphase,hc⟩ := allocate_state hb (by simpa [Packets.Inv,hs] using hf) ho oldkey hn
  have ce : c=⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ := by cases c; simp_all
  subst c
  exact ⟨o,hc,ho,word,RxOrigin.admission_execution _ _ _ _ _ _ hr⟩


private theorem any_spec (a : M α) : ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro; intros; trivial

theorem receiveKey_peer (entry : Option (IndexOwner × PeerId))
    (hr : (Affiliation.receiveKeyAcquire entry).run w=.ok ((kp,pid),v)) : pid=entry.map Prod.snd := by
  have hs : ⦃fun _ => ⌜True⌝⦄ Affiliation.receiveKeyAcquire entry
      ⦃⇓? r _ => ⌜r.2=entry.map Prod.snd⌝⦄ := by
    have hg := fun k => any_spec (keypairGet k)
    have hn := any_spec keypairGetCurrent
    cases entry with
    | none => mvcgen [Affiliation.receiveKeyAcquire,hn]
    | some e =>
      rcases e with ⟨owner,p⟩
      cases owner <;> mvcgen [Affiliation.receiveKeyAcquire,hg,invariant]
      all_goals simp_all
  exact (hoare_iff_triple _ _ _).mpr hs w _ v True.intro hr

/-- Repayment consumes precisely the actual lookup loan. The initial positive
count makes this repayment nonfinal; no independent residency premise. -/
theorem loan_repay_state (hi : CarrierState cs loans w) (hl : Loan w pid u)
    (hk : KeyEffect NoPromotion w u) (hr : (peerPut pid).run u=.ok ((),v)) :
    CarrierState cs loans v := by
  cases pid with
  | none =>
    have he : v=CounterWindow.record u .peerPutNull true := by simpa [peerPut] using hr.symm
    have hu : CarrierState cs loans u := ⟨inventory_view hi.inventory hl.2,queueOwners_view hi.queues hl.1,
      protected_view hi.funded hl.1,hk.rxCompatible hl.2 hi.keys.1,
      hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩
    exact hu.kernel (by rw [he]; rfl)
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
    have paid := peerPut_handoff hdu hpu count hr
    have hx := paid.rx.trans hrx
    have hb := paid.base.trans (loan_base (result:=some pid) ⟨d,p,hd,hp,pos,hview,hrx⟩)
    have he := hk.trans (peerPut_keyEffect (some pid) u () v hr)
    refine ⟨inventory_view hi.inventory hx,queueOwners_base hi.queues hb,?_,
      he.rxCompatible hx hi.keys.1,he.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩
    intro owner
    rw [credit_repayment hd hp pos hview hr owner]
    exact hi.funded owner

structure AdmissionFront (initial : World) (pid : Option PeerId) (w : World) : Prop where
  loan : Loan initial pid w
  keys : KeyEffect NoPromotion initial w

theorem AdmissionFront.kernel (h : AdmissionFront initial pid w) (hk : v.k=w.k) : AdmissionFront initial pid v := by
  exact ⟨loan_after_frame h.loan (by unfold peerView; rw [hk]) (by unfold rxView; rw [hk]),
    h.keys.trans (keyEffect_of_view (by unfold keyView keyWords currentCells; rw [hk]))⟩

theorem AdmissionFront.keyPut (h : AdmissionFront initial pid w)
    (hr : (keypairPut kp now).run w=.ok ((),v)) : AdmissionFront initial pid v := by
  have hf := Prod.mk.inj (keypairPut_credit_frame kp now w () v hr)
  exact ⟨loan_after_frame h.loan hf.1 hf.2,h.keys.trans (keypairPut_keyEffect kp now w () v hr)⟩

theorem lookup_front (hr : (indexLookup kinds index).run w=.ok (entry,a))
    (ha : (Affiliation.receiveKeyAcquire entry).run a=.ok ((kp,pid),b)) : AdmissionFront w pid b := by
  have hl := (hoare_iff_triple _ _ _).mpr (indexLookup_loan kinds index w) w entry a rfl hr
  have hp := receiveKey_peer entry ha
  have hf := Prod.mk.inj (receiveKey_credit_frame entry a _ b ha)
  exact ⟨loan_after_frame (hp ▸ hl) hf.1 hf.2,
    (indexLookup_keyEffect kinds index w entry a hr).trans (keyEffect_of_view (receiveKey_keyView entry a _ b ha))⟩

/-- The original no-key and dead-peer normal returns restore the supplied
carrier ledger by repaying the actual lookup reference. They need not roll
back key invalidation, owner store-back or recorded branches. -/
theorem admitted_none (hi : CarrierState cs loans w)
    (hr : (RxOrigin.admitSource msg src ds).run w=.ok (none,v)) : CarrierState cs loans v := by
  rw [RxOrigin.admitSource_factor] at hr
  obtain ⟨entry,a,hl,acquired,b,hk,noKey,c,hn,rest⟩ := (by simpa only [MaterialOrigin.bind_ok] using hr)
  rcases acquired with ⟨kp,pid⟩
  have front := lookup_front hl hk
  have kc := sameKernel_branch .dataNoKeypair kp.isNone b noKey c hn
  have fc := front.kernel kc
  cases noKey with
  | true =>
    simp only [↓reduceIte,MaterialOrigin.bind_ok] at rest
    obtain ⟨u,z,hpay,he⟩ := rest
    cases u
    have zv : z=v := by simpa using he
    subst z
    exact loan_repay_state hi fc.loan fc.keys hpay
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at rest
    cases kp with
    | none => simp [invariant] at rest
    | some kid =>
      cases pid with
      | none => simp [invariant] at rest
      | some pid =>
        obtain ⟨peer,d,hread,dead,e,hdead,rest⟩ := (by simpa only [MaterialOrigin.bind_ok] using rest)
        have kd := (getPeer_normal pid c d peer hread).1
        have ke := sameKernel_branch .dataPeerDead peer.isDead d dead e hdead
        have fe := (fc.kernel (congrArg World.k kd)).kernel ke
        cases dead with
        | true =>
          simp only [↓reduceIte,MaterialOrigin.bind_ok] at rest
          obtain ⟨u,f,hkey,u,g,hpay,he⟩ := rest
          cases u
          have gv : g=v := by simpa using he
          subst g
          exact loan_repay_state hi (fe.keyPut hkey).loan (fe.keyPut hkey).keys hpay
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,MaterialOrigin.bind_ok] at rest
          obtain ⟨slot,z,ha,bad⟩ := rest
          simp at bad

end Leanux.Proofs.WG.Queues.RxCredits
