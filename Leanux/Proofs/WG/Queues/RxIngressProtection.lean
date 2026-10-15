import Leanux.Proofs.WG.Queues.RxCleanupProtection

/-! Actual index-acquired peer loans and RX admission cuts. The successful
fresh store-back supplies the key's owner word locally. No initialized
ownership, cryptographic affiliation or retrospective reference slack is used. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

def creditKernel (k : Kernel) (d : Device) (pid : PeerId) (p : Peer) : Kernel :=
  {k with wg := some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}}}

/-- The actual get adds one credit; the fresh owner setter may change its word
but preserves peer identity/count/queues and every resident RX cell. -/
def Loan (before : World) (result : Option PeerId) (after : World) : Prop :=
  match result with
  | none => peerView after = peerView before ∧ rxView after = rxView before
  | some pid => ∃ d p, before.k.wg = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      peerView after = peerView {before with k := creditKernel before.k d pid p} ∧
      rxView after = rxView before

theorem ownerStore_credit_frame (owner : IndexOwner) (word : Option PeerId) :
    SameView (fun w => (peerView w,rxView w)) (owner.setPeerWord word) := by
  apply SameView.of_wp
  intro s
  cases owner <;> mvcgen [IndexOwner.setPeerWord,getPeer,getKeypair,getDev,getK,setPeer,setKeypair,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [peerView,rxView]
  all_goals subst_vars
  all_goals simp_all [peerView,rxView]
  all_goals funext q
  all_goals simp only [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all

theorem acquireOwner_loan (owner : IndexOwner) (w v : World) (result : Option PeerId)
    (hr : (Affiliation.acquireOwner owner).run w = .ok (result,v)) : Loan w result v := by
  obtain ⟨word,a,b,hread,hget,hstore⟩ := Affiliation.acquireOwner_acquisition owner w v result hr
  have hk := indexOwner_peerWord_sameKernel owner w word a hread
  have hb := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec word a.k) a result b rfl hget
  have hs := Prod.mk.inj (ownerStore_credit_frame owner result b () v hstore)
  cases result with
  | none =>
    have he : b.k = w.k := hb.2.trans hk
    exact ⟨hs.1.trans (by simp [peerView,he]),hs.2.trans (by simp [rxView,he])⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,hpos,he⟩ := hb.2
    refine ⟨d,p,hk ▸ hd,hp,hpos,?_,?_⟩
    · exact hs.1.trans (by simp [peerView,creditKernel,he,hk])
    · have hdw : w.k.wg = some d := hk ▸ hd
      exact hs.2.trans (by simp [rxView,he,hk,hdw])

theorem acquireOwner_loan_spec (owner : IndexOwner) (initial : World) :
    ⦃fun w => ⌜w.k = initial.k⌝⦄ Affiliation.acquireOwner owner
    ⦃⇓? result w => ⌜Loan initial result w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v hk hr
  have h := acquireOwner_loan owner w v result hr
  cases result <;> simpa [Loan,peerView,rxView,creditKernel,hk] using h

/-- Complete literal index scan: its returned peer carries exactly the source
loan, including the ordinary None arm after a failed nullable acquisition. -/
theorem indexLookup_loan (kinds : List IndexKind) (index : Nat) (initial : World) :
    ⦃fun w => ⌜w.k = initial.k⌝⦄ indexLookup kinds index
    ⦃⇓? result w => ⌜Loan initial (result.map Prod.snd) w⌝⦄ := by
  rw [← Affiliation.indexLookupSource_eq]
  have hb := fun decision value => sameKernel_wp _ (sameKernel_branch decision value) (fun k => k = initial.k)
  have hi := sameKernel_wp _ (indexBucket_sameKernel index) (fun k => k = initial.k)
  have ha := fun owner => acquireOwner_loan_spec owner initial
  mvcgen [Affiliation.indexLookupSource,hb,hi,ha,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜w.k = initial.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Loan,peerView,rxView]

/-- Source store-back, not a global affiliation premise: a returned key owner
has the borrowed peer word in the actual acquisition endpoint. -/
theorem acquireOwner_key_word (id pid : Nat) (w v : World)
    (hr : (Affiliation.acquireOwner (.keypair id)).run w = .ok (some pid,v)) :
    ∃ d k, v.k.wg = some d ∧ d.keypairs[id]? = some k ∧ k.peer = some pid := by
  obtain ⟨word,a,b,hread,hget,hstore⟩ := Affiliation.acquireOwner_acquisition _ _ _ _ hr
  obtain ⟨d,k,hd,hk,hv⟩ := Origins.keypair_word_store id (some pid) b v hstore
  subst v
  refine ⟨{d with keypairs := d.keypairs.insert id {k with peer := some pid}},
    {k with peer := some pid},?_,?_,rfl⟩
  · simp [CounterWindow.store,hd]
  · simp

theorem credit_balance (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (o : Owner) : balance {w with k := creditKernel w.k d pid p} o =
      if o = ⟨d.ifindex,pid,p.internalId⟩ then balance w o + 1 else balance w o := by
  rcases o with ⟨epoch,slot,stamp⟩
  simp only [balance_factor,peerView,viewBalance,creditKernel,hd,Option.map_some,Option.bind_some]
  by_cases he : d.ifindex = epoch <;> by_cases hi : pid = slot <;>
    by_cases hs : p.internalId = stamp
  all_goals simp_all [Std.TreeMap.getElem?_insert,Owner.mk.injEq]
  all_goals grind

/-- An actual lookup loan extends the given reservation ledger; the extra
reference is never reconstructed from arbitrary endpoint slack. -/
theorem loan_protected (hl : Loan w (some pid) v) (hi : Protected cs loans w) :
    ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Protected cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,hd,hp,pos,hv,_⟩ := hl
  refine ⟨d,p,hd,hp,pos,?_⟩
  intro o
  have he := (balance_view (o := o) hv).trans (credit_balance hd hp o)
  have old := hi o
  by_cases ho : o = ⟨d.ifindex,pid,p.internalId⟩
  · simp [demand,ho] at *
    omega
  · simp [demand,List.count_cons,ho,Ne.symm ho] at *
    omega

theorem loan_to_carrier (hi : Protected cs (c.owner :: loans) w)
    (hc : c.phase.charged = true) : Protected (c :: cs) loans w := by
  intro o
  have old := hi o
  by_cases he : c.owner = o <;> simp [demand,hc,he,List.count_cons] at * <;> omega

/-- A genuinely vacant allocation slot extends this same complete inventory.
The caller may obtain vacancy from the existing packet allocation invariant. -/
theorem allocate_inventory (hi : Inventory cs w) (hd : w.k.wg = some d)
    (fresh : d.rxSkbs[d.nextSkb]? = none) (owner : o.epoch = d.ifindex)
    (pid : pkt.peer = o.slot) :
    let c : Carrier := ⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩
    let v := Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}
    (newRxSkb pkt).run w = .ok (d.nextSkb,v) ∧ Inventory (c :: cs) v ∧
      peerView v = peerView w := by
  dsimp only
  let c : Carrier := ⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩
  let v := Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}
  have different : ∀ x ∈ cs, x.packet ≠ c.packet := by
    intro x hx he
    obtain ⟨_,q,hq,_⟩ := hi.present x hx
    rw [he] at hq
    simp [c,packetAt,hd,fresh] at hq
  have keeps : ∀ x ∈ cs, packetAt v x.packet = packetAt w x.packet := by
    intro x hx
    obtain ⟨_,q,hq,_⟩ := hi.present x hx
    have epoch : d.ifindex = x.packet.epoch := by
      by_cases he : d.ifindex = x.packet.epoch
      · exact he
      · simp [packetAt,hd,he] at hq
    have ne : d.nextSkb ≠ x.packet.slot := by
      intro he
      apply different x hx
      cases hx : x.packet
      simp_all [c,Packet.mk.injEq]
    simp [v,packetAt,Packets.update,hd,epoch,Std.TreeMap.getElem?_insert,ne]
  refine ⟨by simpa [Packets.update,hd] using Packets.newRxSkb_run w d pkt hd,?_,by simp [v,peerView,Packets.update,hd]⟩
  refine ⟨?_,?_,?_⟩
  · simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,hi.distinct⟩
    intro hm
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    exact different x hx he
  · intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      exact ⟨owner.symm,pkt,by simp [packetAt,Packets.update,hd],pid⟩
    · obtain ⟨ep,q,hq,ho⟩ := hi.present x hx
      exact ⟨ep,q,(keeps x hx).trans hq,ho⟩
  · intro out id q hout hq
    have oe : out = {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1} := by simpa [Packets.update,hd] using hout.symm
    subst out
    by_cases he : d.nextSkb = id
    · exact ⟨c,by simp [c],by simp [c,he]⟩
    · have old : d.rxSkbs[id]? = some q := by simpa [Std.TreeMap.getElem?_insert,he] using hq
      obtain ⟨x,hx,h⟩ := hi.complete d id q hd old
      exact ⟨x,by simp [hx],h⟩

/-- Allocation transfers the already-attributed lookup reservation into one
unpublished carrier, retaining the given inventory and every other charge. -/
theorem allocate_transfer (hi : Inventory cs w) (hd : w.k.wg = some d)
    (fresh : d.rxSkbs[d.nextSkb]? = none) (owner : o.epoch = d.ifindex)
    (pid : pkt.peer = o.slot) (hs : Protected cs (o :: loans) w) :
    ∃ v, (newRxSkb pkt).run w = .ok (d.nextSkb,v) ∧
      Inventory (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) v ∧
      Protected (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) loans v := by
  obtain ⟨hr,iv,hv⟩ := allocate_inventory hi hd fresh owner pid
  exact ⟨_,hr,iv,protected_view (loan_to_carrier hs rfl) hv⟩

/-- Current key word at a concrete successful acquisition boundary. -/
def KeyWord (kid pid : Nat) (w : World) : Prop :=
  ∃ d k, w.k.wg = some d ∧ d.keypairs[kid]? = some k ∧ k.peer = some pid

theorem acquire_key_spec (owner : IndexOwner) :
    ⦃fun _ => ⌜True⌝⦄ Affiliation.acquireOwner owner
    ⦃⇓? result w => ⌜∀ kid pid, owner = .keypair kid → result = some pid → KeyWord kid pid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v _ hr kid pid he hp
  subst owner; subst result
  exact acquireOwner_key_word kid pid w v hr

/-- The full original lookup stores the borrowed peer into the actual returned
key owner. It does not assume an initialized global affiliation invariant. -/
theorem indexLookup_key_word (kinds : List IndexKind) (index : Nat) :
    ⦃fun _ => ⌜True⌝⦄ indexLookup kinds index
    ⦃⇓? result w => ⌜∀ kid pid, result = some (.keypair kid,pid) → KeyWord kid pid w⌝⦄ := by
  rw [← Affiliation.indexLookupSource_eq]
  have ha := acquire_key_spec
  mvcgen [Affiliation.indexLookupSource,ha,indexBucket,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ _ => ⌜True⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [KeyWord]

theorem keypairGet_credit_frame (kid : Option KeypairId) :
    SameView (fun w => (peerView w,rxView w)) (keypairGet kid) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountIncNotZero,branchCmp,branchCmpExcluded,branch,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [peerView,rxView]

theorem receiveKey_credit_frame (entry : Option (IndexOwner × PeerId)) :
    SameView (fun w => (peerView w,rxView w)) (Affiliation.receiveKeyAcquire entry) := by
  have hk := fun kid => (keypairGet_credit_frame kid).wp
  have hn : SameView (fun w => (peerView w,rxView w)) keypairGetCurrent := by
    intro w x v hr
    have he := Lifetimes.keypairGetCurrent_sameKernel w x v hr
    simp [peerView,rxView,he]
  cases entry with
  | none =>
    simpa [Affiliation.receiveKeyAcquire] using hn.bind (fun _ => SameView.pure _ _)
  | some e =>
    rcases e with ⟨owner,pid⟩
    cases owner
    · apply SameView.of_wp
      intro s
      mvcgen [Affiliation.receiveKeyAcquire,invariant]
    · simpa [Affiliation.receiveKeyAcquire] using
        (keypairGet_credit_frame (some _)).bind (fun _ => SameView.pure _ _)

theorem loan_after_frame (hl : Loan w pid a)
    (hv : peerView b = peerView a) (hx : rxView b = rxView a) : Loan w pid b := by
  cases pid with
  | none => exact ⟨hv.trans hl.1,hx.trans hl.2⟩
  | some pid =>
    obtain ⟨d,p,hd,hp,pos,he,hr⟩ := hl
    exact ⟨d,p,hd,hp,pos,hv.trans he,hx.trans hr⟩

/-- Every actual normal admission reaches allocation with exactly the lookup's
peer loan and the actual packet. The intermediate Worlds are consecutive source
cuts, retained independently of whether enqueue or later cleanup succeeds. -/
theorem admitted_loan (hr : (RxOrigin.admitSource msg src ds).run w = .ok (some ctx,v)) :
    ∃ before, Loan w (some ctx.packet.peer) before ∧
      (newRxSkb ctx.packet).run before = .ok (ctx.slot,v) := by
  obtain ⟨entry,a,b,c,peer,d,e,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v hr
  have entryEq := ((hoare_iff_triple _ _ _).mpr
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a))
    a _ b rfl hk).2 ctx.packet.keypair ctx.packet.peer rfl
  have loan := (hoare_iff_triple _ _ _).mpr (indexLookup_loan [.keypair] (u32le msg 4) w)
    w entry a rfl hl
  have fr := Prod.mk.inj (receiveKey_credit_frame entry a _ b hk)
  have lc : Loan w (some ctx.packet.peer) b := loan_after_frame (by simpa [entryEq] using loan) fr.1 fr.2
  have kc := sameKernel_branch .dataNoKeypair false b false c hno
  obtain ⟨he,_,_,_⟩ := getPeer_normal ctx.packet.peer c d peer hp
  have ke := sameKernel_branch .dataPeerDead peer.isDead d false e hd
  refine ⟨e,loan_after_frame lc ?_ ?_,hn⟩
  all_goals simp [peerView,rxView,ke,he,kc]

def publicationMiddle (pid : PeerId) (id : SkbId) (state : PacketState) : M Unit := do
  let p ← getPeer pid
  if !(p.rxQueue.all.contains id) then invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => {q with state}
  setPeer pid {p with napiScheduled := true}

theorem publicationMiddle_frame (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView peerView (publicationMiddle pid id state) := by
  apply SameView.of_wp
  intro s
  mvcgen [publicationMiddle,getPeer,getRxSkb,setRxSkb,getDev,getK,setPeer,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [peerView]
  all_goals subst_vars
  all_goals simp_all [peerView]
  all_goals funext q
  all_goals simp only [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all

theorem publication_factor (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx (pure ()) id state = (do
      let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
      peerGet pid
      publicationMiddle pid id state
      peerPut (some pid)) := by
  simp only [enqueuePerPeerRx,publicationMiddle,bind_assoc,pure_bind]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc,pure_bind]; done)

/-- Repay the same acquired credit after operations preserving the concrete
peer count/identity view. The preserved projection is a local source contract. -/
theorem credit_repayment (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (pos : 0 < p.refcount)
    (view : peerView b = peerView {w with k := creditKernel w.k d pid p})
    (hr : (peerPut (some pid)).run b = .ok ((),v)) :
    ∀ o, balance v o = balance w o := by
  have ep := (Prod.mk.inj view).1
  have slot := congrFun (Prod.mk.inj view).2 pid
  cases hb : b.k.wg with
  | none => simp [peerView,hb,creditKernel] at ep
  | some db =>
    have epoch : db.ifindex = d.ifindex := by simpa [peerView,hb,creditKernel] using ep
    cases hg : db.peers[pid]? with
    | none => simp [peerView,hb,hg,creditKernel] at slot
    | some q =>
      have fields : q.internalId = p.internalId ∧ q.refcount = p.refcount + 1 ∧ q.rxQueue = p.rxQueue := by
        simpa [peerView,hb,hg,creditKernel] using slot
      have positive : 0 < q.refcount := by omega
      have effect := (peerPut_effect pid b v db q hb hg hr).2.1
      intro o
      have hv := (balance_view (o := o) effect).trans (payment_balance hb hg positive o)
      have bv := (balance_view (o := o) view).trans (credit_balance hd hp o)
      rw [epoch,fields.1] at hv
      by_cases he : o = ⟨d.ifindex,pid,p.internalId⟩
      · subst o
        simp only [ite_true] at hv bv
        omega
      · simp only [if_neg he] at hv bv
        omega

/-- The pure-IRQ publication path pays its own freshly acquired reference,
for the actual resolved peer; it need not equal an assumed packet owner. -/
theorem publication_balances (id : SkbId) (state : PacketState) (w v : World)
    (hr : (enqueuePerPeerRx (pure ()) id state).run w = .ok ((),v)) :
    ∀ o, balance v o = balance w o := by
  rw [publication_factor] at hr
  simp only [MaterialOrigin.bind_ok] at hr
  obtain ⟨pkt,a,hpkt,pid,b,hderef,_,c,hget,_,e,hmid,hput⟩ := hr
  have ka := (Packets.getRxSkb_current id w a pkt hpkt).1
  subst a
  have kb := indexOwner_peerDeref_sameKernel (.keypair pkt.keypair) w pid b hderef
  obtain ⟨d,p,hd,hp,pos,hc⟩ := peerGet_loan pid b c hget
  have hm := publicationMiddle_frame pid id state c () e hmid
  have hv : peerView e = peerView {w with k := creditKernel w.k d pid p} := by
    exact hm.trans (by simp [peerView,creditKernel,hc,kb])
  exact credit_repayment (kb ▸ hd) hp pos hv hput

theorem keyWord_affiliation_view (hw : KeyWord kid pid w)
    (he : Affiliation.view v = Affiliation.view w) : KeyWord kid pid v := by
  obtain ⟨d,k,hd,hk,hp⟩ := hw
  have hs := congrArg (fun o => o.bind fun s => s.keys kid) he
  cases hv : v.k.wg with
  | none => simp [Affiliation.view,Affiliation.state,hd,hv,hk] at hs
  | some dv =>
    cases hvk : dv.keypairs[kid]? with
    | none => simp [Affiliation.view,Affiliation.state,hd,hv,hk,hvk] at hs
    | some kv =>
      have words : kv.peer = k.peer := by
        have h : Affiliation.keyCell kv = Affiliation.keyCell k := by
          simpa [Affiliation.view,Affiliation.state,hd,hv,hk,hvk] using hs
        exact congrArg Prod.snd h
      exact ⟨dv,kv,hv,hvk,words.trans hp⟩

/-- The actual admitted key keeps the successful lookup's locally stored owner
through key acquisition and RX allocation; no global affiliation premise. -/
theorem admitted_key_word (hr : (RxOrigin.admitSource msg src ds).run w = .ok (some ctx,v)) :
    KeyWord ctx.packet.keypair ctx.packet.peer v := by
  obtain ⟨entry,a,b,c,peer,d,e,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v hr
  have ka := (hoare_iff_triple _ _ _).mpr
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view a)) a _ b rfl hk
  have ent := ka.2 ctx.packet.keypair ctx.packet.peer rfl
  have wa := (hoare_iff_triple _ _ _).mpr (indexLookup_key_word [.keypair] (u32le msg 4))
    w entry a True.intro hl _ _ ent
  have wb := keyWord_affiliation_view wa ka.1
  have kc := sameKernel_branch .dataNoKeypair false b false c hno
  obtain ⟨he,_,_,_⟩ := getPeer_normal ctx.packet.peer c d peer hp
  have ke := sameKernel_branch .dataPeerDead peer.isDead d false e hd
  have we : KeyWord ctx.packet.keypair ctx.packet.peer e := by
    simpa [KeyWord,ke,he,kc] using wb
  obtain ⟨dev,key,hdev,hkey,hword⟩ := we
  rw [Packets.newRxSkb_run e dev ctx.packet hdev] at hn
  have hv := (Prod.mk.inj (Except.ok.inj hn)).2
  rw [← hv]
  exact ⟨{dev with rxSkbs := dev.rxSkbs.insert dev.nextSkb ctx.packet, nextSkb := dev.nextSkb + 1},
    key,by simp [Packets.update,hdev],hkey,hword⟩

/-- The original post-allocation tail, already factored by the receipt layer. -/
def finishSource (ctx : RxOrigin.Admission) : M Unit :=
  RxOrigin.finishWith keypairPut WG.peerPut enqueuePerDeviceAndPeerRx
    (fun id => enqueuePerPeerRx (pure ()) id .dead) freeRxSkb (fun a => a) ctx

def enospcDecisions (w : World) : World :=
  CounterWindow.record (CounterWindow.record (CounterWindow.record w .dataEpipe false)
    .dataEnqueueOk false) .dataEnqueueOkEpipe false

/-- The negative errno still executes all three recorded decisions, then the
actual key-put/peer-put/free suffix. No successful cleanup endpoint is assumed. -/
theorem finish_enospc (ctx : RxOrigin.Admission)
    (hr : (enqueuePerDeviceAndPeerRx ctx.slot).run w = .ok (-ENOSPC,a)) :
    (finishSource ctx).run w = (discard ctx.slot ctx.packet).run (enospcDecisions a) := by
  simp [finishSource,RxOrigin.finishWith,StateT.run_bind,hr,WG.orM,branch,
    ENOSPC,EPIPE,discard,enospcDecisions,CounterWindow.record]

/-- Concrete ENOSPC source repayment/free from the actual enqueue endpoint.
The supplied unpublished ledger is retained, never reconstructed from counts. -/
theorem enospc_discharge (ctx : RxOrigin.Admission)
    (hr : (enqueuePerDeviceAndPeerRx ctx.slot).run w = .ok (-ENOSPC,a))
    (hi : Inventory (c :: cs) a) (hs : Protected (c :: cs) loans a)
    (hq : QueueOwners (c :: cs) a) (phase : c.phase = .unpublished)
    (slot : c.packet.slot = ctx.slot) (owner : ctx.packet.peer = c.owner.slot)
    (hk : (keypairPut (some ctx.packet.keypair) false).run (enospcDecisions a) = .ok ((),b)) :
    ∃ v, (finishSource ctx).run w = .ok ((),v) ∧ Inventory cs v ∧
      Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none := by
  have iv : Inventory (c :: cs) (enospcDecisions a) := inventory_view hi rfl
  have sv : Protected (c :: cs) loans (enospcDecisions a) := protected_view hs rfl
  have qv : QueueOwners (c :: cs) (enospcDecisions a) := queueOwners_view hq rfl
  obtain ⟨v,hv,iv,sv,qv,pv⟩ := discard_unpublished iv sv qv phase owner hk
  refine ⟨v,?_,iv,sv,qv,pv⟩
  rw [finish_enospc ctx hr]
  simpa [slot] using hv

end Leanux.Proofs.WG.Queues.RxCredits
