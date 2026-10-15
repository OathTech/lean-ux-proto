import Leanux.Proofs.WG.Queues.RxAdmissionCarrier

/-! Actual postallocation queue installation and disposal. Negative errno
returns are source outcomes; a Stop has no returned World. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

def enqueueDevice (d : Device) (id : SkbId) (pkt : RxPacket) (p : Peer) (ret : Int) (cpu : Int) : Device :=
  { d with
    rxSkbs := d.rxSkbs.insert id ({ pkt with state := .uncrypted })
    peers := (if ret = -ENOSPC then d.peers else d.peers.insert pkt.peer ({ p with rxQueue := p.rxQueue.enqueue id }))
    decryptLastCpu := (if ret = -ENOSPC then d.decryptLastCpu else cpu)
    decryptQueue := (if ret=0 then d.decryptQueue.produce id else d.decryptQueue) }

theorem enqueue_effect {id : SkbId} (hd : w.k.wg=some d) (hs : d.rxSkbs[id]?=some pkt)
    (hp : d.peers[pkt.peer]?=some p)
    (hr : (enqueuePerDeviceAndPeerRx id).run w=.ok (ret,v)) :
    (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
    ∃ cpu, v.k={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)} := by
  have post : ⦃fun z => ⌜z.k=w.k⌝⦄ enqueuePerDeviceAndPeerRx id
      ⦃⇓? ret z => ⌜(ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        ∃cpu,z.k={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}⌝⦄ := by
    have hc := fun cpu k => sameKernel_wp _ (cpumaskNextOnlineFrom_sameKernel cpu) (fun q => q=k)
    have hq := fun k => sameKernel_wp _ (queueDeviceWork_sameKernel .decryptWorker) (fun q => q=k)
    mvcgen [enqueuePerDeviceAndPeerRx,setRxSkb,getRxSkb,getPeer,getDev,getK,setPeer,
      modifyDev,modifyK,branch,invariant,hc,hq]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [enqueueDevice,hd,hs,hp,ENOSPC,EPIPE,WG.ENOSPC,WG.EPIPE,Std.TreeMap.getElem?_insert]
    all_goals subst_vars
    all_goals dsimp only at *
    all_goals simp_all
    all_goals first | exact ⟨_,rfl⟩ | (subst_vars; simp_all)
  exact (hoare_iff_triple _ _ _).mpr post w ret v rfl hr


def rxShape (w : World) := (w.k.wg.map (·.ifindex),fun id : SkbId =>
  (w.k.wg.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))

theorem packet_shape (he : rxShape v=rxShape w) (p : Packet) :
    (packetAt v p).map (fun q => (q.peer,q.keypair)) =
      (packetAt w p).map (fun q => (q.peer,q.keypair)) := by
  have ep := congrArg Prod.fst he
  have hs := congrFun (congrArg Prod.snd he) p.slot
  cases hv : v.k.wg <;> cases hw : w.k.wg <;>
    simp_all [rxShape,packetAt]
  split <;> simp_all
  exact congrFun he.2 p.slot

theorem inventory_shape (hi : Inventory cs w) (he : rxShape v=rxShape w) : Inventory cs v := by
  refine ⟨hi.distinct,?_,?_⟩
  · intro c hc
    obtain ⟨ep,p,hp,ho⟩ := hi.present c hc
    have hs := packet_shape he c.packet
    rw [hp] at hs
    obtain ⟨q,hq,hfields⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨ep,q,hq,(congrArg Prod.fst hfields).trans ho⟩
  · intro d id p hd hp
    have ep := congrArg Prod.fst he
    have hs := congrFun (congrArg Prod.snd he) id
    have old : ((w.k.wg.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))=some (p.peer,p.keypair) := by
      simpa [rxShape,hd,hp] using hs.symm
    obtain ⟨q,hq,_⟩ := Option.map_eq_some_iff.mp old
    obtain ⟨od,hod,hoq⟩ := Option.bind_eq_some_iff.mp hq
    have epoch : d.ifindex=od.ifindex := by simpa [rxShape,hd,hod] using ep
    obtain ⟨c,hc,he⟩ := hi.complete od id q hod hoq
    exact ⟨c,hc,by simpa [epoch] using he⟩

theorem rxCompatible_shape (hi : RxCompatible w) (he : rxShape v=rxShape w)
    (hk : KeyEffect allowed w v) : RxCompatible v := by
  intro d id p hd hp
  have hs := congrFun (congrArg Prod.snd he) id
  have old : ((w.k.wg.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))=some (p.peer,p.keypair) := by
    simpa [rxShape,hd,hp] using hs.symm
  obtain ⟨q,hq,eq⟩ := Option.map_eq_some_iff.mp old
  obtain ⟨od,hod,hoq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨hpeer,hkey⟩ := Prod.mk.inj eq
  simpa [←hpeer,←hkey] using hk.compatible (hi od id q hod hoq)

def enqueued (c : Carrier) : Carrier := {c with phase:=.queued}

theorem inventory_enqueued (hi : Inventory (c::cs) w) : Inventory (enqueued c::cs) w := by
  refine ⟨by simpa [enqueued] using hi.distinct,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa [enqueued] using hi.present c (by simp)
    · exact hi.present x (by simp [hx])
  · intro d id p hd hp
    obtain ⟨x,hx,he⟩ := hi.complete d id p hd hp
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨enqueued x,by simp,by simpa [enqueued] using he⟩
    · exact ⟨x,by simp [hx],he⟩

theorem enqueue_shape {id : SkbId} (hd : w.k.wg=some d) (hs : d.rxSkbs[id]?=some pkt) :
    rxShape {w with k:={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}}=rxShape w := by
  simp only [rxShape,hd,enqueueDevice,Option.map_some,Option.bind_some]
  congr 1
  funext j
  by_cases he : id=j <;> simp_all [Std.TreeMap.getElem?_insert]

theorem enqueueDevice_keyView {id : SkbId} (hd : w.k.wg=some d) (hp : d.peers[pkt.peer]?=some p) :
    keyView {w with k:={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}}=keyView w := by
  unfold keyView keyWords currentCells
  simp only [hd,enqueueDevice,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases ret=-ENOSPC <;> by_cases pkt.peer=q <;>
    simp_all [Std.TreeMap.getElem?_insert,currentCell]

theorem enqueue_balance {id : SkbId} (hd : w.k.wg=some d) (hp : d.peers[pkt.peer]?=some p) (o : Owner) :
    balance {w with k:={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}} o=balance w o := by
  simp only [balance,resident,hd,enqueueDevice,Option.bind_some]
  by_cases ret=-ENOSPC <;> by_cases pkt.peer=o.slot <;>
    simp_all [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem enqueue_queues {id : SkbId} (hi : QueueOwners (c::cs) w) (hc : c.phase=.unpublished)
    (hd : w.k.wg=some d) (hp : d.peers[pkt.peer]?=some p)
    (packet : c.packet=⟨d.ifindex,id⟩) (owner : c.owner=⟨d.ifindex,pkt.peer,p.internalId⟩) :
    QueueOwners ((if ret=-ENOSPC then c else enqueued c)::cs)
      {w with k:={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}} := by
  intro out q peer j hout hpeer
  have eq : out=enqueueDevice d id pkt p ret cpu := Option.some.inj hout.symm
  subst out
  by_cases hr : ret=-ENOSPC
  · simpa [enqueueDevice,hr] using hi d q peer j hd (by simpa [enqueueDevice,hr] using hpeer)
  · by_cases hq : pkt.peer=q
    · subst q
      have he : peer={p with rxQueue:=p.rxQueue.enqueue id} := by
        simpa [enqueueDevice,hr] using hpeer.symm
      subst peer
      have old := hi d pkt.peer p j hd hp
      simp only [List.filter_cons,hc,Bool.and_false,↓reduceIte] at old
      have qe : (p.rxQueue.enqueue id).all=p.rxQueue.all++[id] := by
        simp [PrevQueue.all,PrevQueue.enqueue,List.append_assoc]
      by_cases hj : id=j
      · subst j
        simpa [enqueueDevice,hr,enqueued,packet,owner,List.filter_cons,qe,List.count_append] using old
      · simpa [enqueueDevice,hr,enqueued,packet,owner,List.filter_cons,qe,List.count_append,hj,Ne.symm hj,Packet.mk.injEq] using old
    · have oldpeer : d.peers[q]?=some peer := by simpa [enqueueDevice,hr,Std.TreeMap.getElem?_insert,hq] using hpeer
      have old := hi d q peer j hd oldpeer
      simpa [enqueueDevice,hr,enqueued,packet,owner,List.filter_cons,hc,hq,Owner.mk.injEq] using old

/-- Actual enqueue changes only this unpublished carrier's phase when the
peer queue accepts it; the original no-space arm leaves it unpublished. -/
theorem enqueue_state (hi : CarrierState (c::cs) loans w) (hc : c.phase=.unpublished)
    (hs : packetAt w c.packet=some pkt) (owner : pkt.peer=c.owner.slot)
    (hr : (enqueuePerDeviceAndPeerRx c.packet.slot).run w=.ok (ret,v)) :
    (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
    CarrierState ((if ret=-ENOSPC then c else enqueued c)::cs) loans v := by
  have charged : 0<demand (c::cs) loans c.owner := by simp [demand,charges,hc,Phase.charged]; omega
  obtain ⟨p,hp,_⟩ := protected_resident hi.funded charged
  obtain ⟨d,hd,epoch,hpeer,stamp⟩ := resident_fields hp
  have ep : d.ifindex=c.packet.epoch := by
    have he := (hi.inventory.present c (by simp)).1
    exact epoch.trans he.symm
  have slot : d.rxSkbs[c.packet.slot]?=some pkt := by simpa [packetAt,hd,ep] using hs
  have hpkt : d.peers[pkt.peer]?=some p := by simpa [owner] using hpeer
  obtain ⟨rets,cpu,hv⟩ := enqueue_effect hd slot hpkt hr
  let u := {w with k:={w.k with wg:=some (enqueueDevice d c.packet.slot pkt p ret cpu)}}
  have ku : v.k=u.k := hv
  have shape := enqueue_shape (p:=p) (ret:=ret) (cpu:=cpu) hd slot
  have keys := keyEffect_of_view (allowed:=NoPromotion) (enqueueDevice_keyView (id:=c.packet.slot) (ret:=ret) (cpu:=cpu) hd hpkt)
  have packet : c.packet=⟨d.ifindex,c.packet.slot⟩ := by
    calc c.packet = ⟨c.packet.epoch,c.packet.slot⟩ := by cases c.packet; rfl
         _ = _ := by rw [ep]
  have own : c.owner=⟨d.ifindex,pkt.peer,p.internalId⟩ := by
    calc c.owner = ⟨c.owner.epoch,c.owner.slot,c.owner.stamp⟩ := by cases c.owner; rfl
         _ = _ := by rw [epoch,owner,stamp]
  have ii := inventory_shape hi.inventory shape
  have inv : Inventory ((if ret=-ENOSPC then c else enqueued c)::cs) u := by
    split <;> first | exact ii | exact inventory_enqueued ii
  refine ⟨rets,(show CarrierState _ loans u from ⟨inv,
    enqueue_queues hi.queues hc hd hpkt packet own,?_,
    rxCompatible_shape hi.keys.1 shape keys,keys.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩).kernel ku⟩
  intro o
  have bal := enqueue_balance (id:=c.packet.slot) (ret:=ret) (cpu:=cpu) hd hpkt o
  have old := hi.funded o
  simp only [u] at *
  rw [bal]
  by_cases hret : ret=-ENOSPC
  · simpa only [if_pos hret] using old
  · by_cases ho : c.owner=o <;> simpa [if_neg hret,demand,charges,enqueued,List.filter_cons,hc,Phase.charged,ho] using old


theorem rxShape_kernel (ha : SameKernel a) : SameView rxShape a := by
  intro w x v hr
  unfold rxShape
  rw [ha w x v hr]

theorem rxShape_peerGet (pid : PeerId) : SameView rxShape (peerGet pid) := by
  intro w x v hr
  cases x
  obtain ⟨d,p,hd,hp,pos,hv⟩ := peerGet_loan pid w v hr
  simp [rxShape,hv,hd]

theorem rxShape_peerPut (pid : Option PeerId) : SameView rxShape (peerPut pid) := by
  apply SameView.of_wp
  intro s
  simp only [peerPut,indexRemove_eq]
  mvcgen [indexUnhash,requireNotPending,getPeer,getDev,getK,setPeer,modifyDev,modifyK,
    refcountDecAndTest,retirePeerUnits,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [rxShape,Option.map_map,Option.bind_map,Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem publicationMiddle_shape (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView rxShape (publicationMiddle pid id state) := by
  apply SameView.of_wp
  intro s
  mvcgen [publicationMiddle,getPeer,getRxSkb,setRxSkb,getDev,getK,setPeer,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [rxShape]
  all_goals subst_vars
  all_goals simp_all [rxShape]
  all_goals funext q
  all_goals by_cases h : id=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem publicationMiddle_keyView (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView keyView (publicationMiddle pid id state) := by
  apply SameView.of_wp
  intro s
  mvcgen [publicationMiddle,getPeer,getRxSkb,setRxSkb,getDev,getK,setPeer,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold keyView keyWords currentCells at *
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all
  all_goals funext q
  all_goals by_cases h : pid=q <;> simp_all [Std.TreeMap.getElem?_insert,currentCell]

theorem publication_preservation (id : SkbId) (state : PacketState)
    (hr : (enqueuePerPeerRx (pure ()) id state).run w=.ok ((),v)) :
    baseView v=baseView w ∧ rxShape v=rxShape w ∧ KeyEffect NoPromotion w v := by
  rw [publication_factor] at hr
  obtain ⟨pkt,a,hpkt,pid,b,hderef,_,c,hget,_,e,hmid,hput⟩ := (by simpa only [MaterialOrigin.bind_ok] using hr)
  have ka := (Packets.getRxSkb_current id w a pkt hpkt).1
  subst a
  have kb := indexOwner_peerDeref_sameKernel (.keypair pkt.keypair) w pid b hderef
  obtain ⟨d,p,hd,hp,pos,hc⟩ := peerGet_loan pid b c hget
  have hdw : w.k.wg=some d := kb ▸ hd
  have hm := publicationMiddle_frame pid id state c () e hmid
  have view : peerView e=peerView {w with k:=creditKernel w.k d pid p} :=
    hm.trans (by simp [peerView,hc,creditKernel,kb])
  let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
  have bal : balance e o=p.refcount+1 := by
    rw [balance_view view,credit_balance hdw hp]
    simp [o,balance,resident,hdw,hp]
  obtain ⟨q,hq⟩ : ∃q,resident e o=some q := by
    cases h : resident e o with
    | none => simp [balance,h] at bal
    | some q => exact ⟨q,rfl⟩
  obtain ⟨de,hde,epoch,hpe,stamp⟩ := resident_fields hq
  have count : 1<q.refcount := by simpa [balance,hq] using (show 1<balance e o by omega)
  have paid := peerPut_handoff hde hpe count hput
  have basecredit : baseView {w with k:=creditKernel w.k d pid p}=baseView w := by
    apply loan_base (result:=some pid)
    exact ⟨d,p,hdw,hp,pos,rfl,by simp [rxView,creditKernel,hdw]⟩
  refine ⟨paid.base.trans ((base_of_peerView view).trans basecredit),?_,?_⟩
  · exact (rxShape_peerPut (some pid) e () v hput).trans
      ((publicationMiddle_shape pid id state c () e hmid).trans
        ((rxShape_peerGet pid b () c hget).trans (by unfold rxShape; rw [kb])))
  · have ke : KeyEffect NoPromotion w e :=
      (keyEffect_of_view (keyView_kernel (indexOwner_peerDeref_sameKernel (.keypair pkt.keypair)) w pid b hderef)).trans
        ((keyEffect_of_view (peerGet_keyView pid b () c hget)).trans
          (keyEffect_of_view (publicationMiddle_keyView pid id state c () e hmid)))
    exact ke.trans (peerPut_keyEffect (some pid) e () v hput)

/-- The actual pure IRQ publication preserves all existing charges while
repaying its separate acquired reference. Packet state and NAPI may change. -/
theorem publication_state {id : SkbId} (hi : CarrierState cs loans w)
    (hr : (enqueuePerPeerRx (pure ()) id state).run w=.ok ((),v)) : CarrierState cs loans v := by
  obtain ⟨hb,hs,hk⟩ := publication_preservation id state hr
  exact ⟨inventory_shape hi.inventory hs,queueOwners_base hi.queues hb,
    (by intro o; rw [publication_balances id state w v hr]; exact hi.funded o),
    rxCompatible_shape hi.keys.1 hs hk,hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩

/-- The normal no-space suffix pays and frees its own unpublished carrier.
The key-put endpoint is extracted from this execution, not assumed separately. -/
theorem discard_state (hi : CarrierState (c::cs) loans w) (hc : c.phase=.unpublished)
    (owner : pkt.peer=c.owner.slot)
    (hr : (discard c.packet.slot pkt).run w=.ok ((),v)) :
    CarrierState cs loans v ∧ packetAt v c.packet=none := by
  have source := hr
  unfold discard at source
  obtain ⟨u,a,hkey,rest⟩ := bind_ok source
  cases u
  obtain ⟨u,b,hpeer,hfree⟩ := bind_ok rest
  cases u
  obtain ⟨out,hout,iv,pv,qv,gone⟩ :=
    discard_unpublished hi.inventory hi.funded hi.queues hc owner hkey
  have he : out=v := by rw [hr] at hout; cases hout; rfl
  subst out
  have ha := keyPut_state _ _ hi hkey
  have ke := peerPut_keyEffect (allowed:=NoPromotion) (some pkt.peer) a () b hpeer
  have kb : KeysCompatible b :=
    ⟨rxCompatible_shape ha.keys.1 (rxShape_peerPut (some pkt.peer) a () b hpeer) ke,
      ke.currentsCompatible ha.keys.2 (by intro p k h; exact h.elim)⟩
  exact ⟨⟨iv,qv,pv,freeRx_keys _ kb hfree⟩,gone⟩

def finishAfter (ctx : RxOrigin.Admission) (ret : Int) : M Unit := do
  if ← branch .dataEpipe (ret == -EPIPE) then
    enqueuePerPeerRx (pure ()) ctx.slot .dead
  if ← WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
  discard ctx.slot ctx.packet

theorem finish_factor (ctx : RxOrigin.Admission) :
    finishSource ctx = (do let ret ← enqueuePerDeviceAndPeerRx ctx.slot; finishAfter ctx ret) := by
  rfl

/-- Every normal original finish has exactly one of the source's three enqueue
outcomes. Success/EPIPE retain the same carrier as queued; ENOSPC disposes it. -/
theorem finish_state (ctx : RxOrigin.Admission) (hi : CarrierState (c::cs) loans w)
    (hc : c.phase=.unpublished) (slot : c.packet.slot=ctx.slot)
    (hs : packetAt w c.packet=some ctx.packet) (owner : ctx.packet.peer=c.owner.slot)
    (hr : (finishSource ctx).run w=.ok ((),v)) :
    ∃ ret a, (enqueuePerDeviceAndPeerRx ctx.slot).run w=.ok (ret,a) ∧
      (finishAfter ctx ret).run a=.ok ((),v) ∧
      (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      (if ret=-ENOSPC then CarrierState cs loans v ∧ packetAt v c.packet=none
       else CarrierState (enqueued c::cs) loans v) := by
  rw [finish_factor] at hr
  obtain ⟨ret,a,he,ht⟩ := bind_ok hr
  obtain ⟨choices,ha⟩ := enqueue_state hi hc hs owner (by simpa [slot] using he)
  refine ⟨ret,a,he,ht,choices,?_⟩
  rcases choices with rfl | rfl | rfl
  · have hv : v=CounterWindow.record (CounterWindow.record a .dataEpipe false) .dataEnqueueOk true := by
      simpa [finishAfter,WG.orM,branch,EPIPE,ENOSPC,CounterWindow.record] using ht.symm
    have state : CarrierState (enqueued c::cs) loans a := by simpa [ENOSPC] using ha
    simpa [ENOSPC] using state.kernel (by rw [hv]; rfl)
  · have run : (discard c.packet.slot ctx.packet).run (enospcDecisions a)=.ok ((),v) := by
      simpa [finishAfter,WG.orM,branch,EPIPE,ENOSPC,enospcDecisions,CounterWindow.record,slot] using ht
    have initial : CarrierState (c::cs) loans a := by simpa using ha
    have state : CarrierState (c::cs) loans (enospcDecisions a) := initial.kernel rfl
    simpa using discard_state state hc owner run
  · simp only [finishAfter,StateT.run_bind,CounterWindow.branch_run] at ht
    simp only [beq_self_eq_true,CounterWindow.except_ok_bind,↓reduceIte] at ht
    obtain ⟨u,b,hpublish,tail⟩ := bind_ok ht
    cases u
    have hb := publication_state
      ((show CarrierState (enqueued c::cs) loans a from by simpa [ENOSPC,EPIPE] using ha).kernel (by rfl)) hpublish
    have hv : v=CounterWindow.record (CounterWindow.record b .dataEnqueueOk false) .dataEnqueueOkEpipe true := by
      simpa [WG.orM,branch,EPIPE,CounterWindow.record] using tail.symm
    simpa [ENOSPC,EPIPE] using hb.kernel (by rw [hv]; rfl)

theorem admitted_packet (hr : (RxOrigin.admitSource msg src ds).run w=.ok (some ctx,v))
    (hp : packetAt v ⟨epoch,ctx.slot⟩=some pkt) : pkt=ctx.packet := by
  obtain ⟨entry,a,b,c,peer,d,e,_,_,_,_,_,_,hn⟩ := RxOrigin.admission_execution _ _ _ _ _ _ hr
  obtain ⟨dev,hd,slot,after,_⟩ :=
    RxOrigin.allocation_record ctx.packet ⟨ctx.slot,e,v⟩ hn
  change e.k.wg=some dev at hd
  change ctx.slot=dev.nextSkb at slot
  change v=Packets.update e _ at after
  rw [after,slot] at hp
  by_cases he : dev.ifindex=epoch
  · simpa [packetAt,Packets.update,hd,he] using hp.symm
  · simp [packetAt,Packets.update,hd,he] at hp

/-- One actual admission receipt determines the complete normal receive result.
The same source-allocated carrier is queued or actually disposed; no endpoint
ledger is reconstructed from spare reference counts. -/
def Consumption (cs : Ledger) (loans : Reservations) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) (w v : World)
    (r : RunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before=w ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after=v ∧ CarrierState cs loans v
  | some ctx => ∃ o,
      let c : Carrier := ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩
      CarrierState (c::cs) loans r.after ∧ o.slot=ctx.packet.peer ∧
      KeyWord ctx.packet.keypair ctx.packet.peer r.after ∧
      RxOrigin.Admitted msg src ds ctx w r.after ∧
      ∃ ret a, (enqueuePerDeviceAndPeerRx ctx.slot).run r.after=.ok (ret,a) ∧
        (finishAfter ctx ret).run a=.ok ((),v) ∧
        (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        (if ret=-ENOSPC then CarrierState cs loans v ∧ packetAt v c.packet=none
         else CarrierState (enqueued c::cs) loans v)

theorem consume_normal (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (hr : (consumeData msg src ds).run w=.ok ((),v)) :
    ∃ r, Consumption cs loans msg src ds w v r := by
  rw [←RxOrigin.consumeSource_eq] at hr
  unfold RxOrigin.consumeSource RxOrigin.consumeWith at hr
  obtain ⟨result,a,hfront,htail⟩ := bind_ok hr
  refine ⟨⟨result,w,a⟩,rfl,hfront,?_⟩
  cases result with
  | none =>
    have he : a=v := by simpa using htail
    subst a
    exact ⟨rfl,admitted_none hi hfront⟩
  | some ctx =>
    obtain ⟨o,ha,owner,word,admitted⟩ := admitted_state hi hf hfront
    obtain ⟨_,pkt,hp,_⟩ := ha.inventory.present
      ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ (by simp)
    have he : pkt=ctx.packet := admitted_packet hfront hp
    subst pkt
    exact ⟨o,ha,owner,word,admitted,finish_state ctx ha rfl rfl hp owner.symm htail⟩

def finishObserved (ctx : RxOrigin.Admission) : RxOrigin.Journal Unit :=
  RxOrigin.finishWith (fun k b => MaterialOrigin.access (keypairPutPrefix k b))
    (fun p => MaterialOrigin.access (peerPutMixed p))
    (fun id => MaterialOrigin.access (enqueuePerDeviceAndPeerRxPrefix id))
    (fun id => MaterialOrigin.access (enqueuePerPeerRxPrefix (pure ()) id .dead))
    (fun id => MaterialOrigin.access (freeRxSkbPrefix id)) liftPrefix ctx

/-- The admission receipt is appended to this execution's actual front output.
Its captured World and value are the same witness used by carrier conservation. -/
theorem observe_admission (r : RunWitness (Option RxOrigin.Admission))
    (hb : r.before=w) (hv : r.Valid (RxOrigin.admitSource msg src ds))
    (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    runPrefix (RxOrigin.observeAdmission msg src ds) w h =
      (.ok (r.value,r.after),
        (runPrefix (RxOrigin.admitRaw msg src ds) w h).2 ++
          [.receipt (.admission msg src ds r)]) := by
  have hr : (RxOrigin.admitSource msg src ds).run w=.ok (r.value,r.after) := by
    simpa [RunWitness.Valid,hb] using hv
  have raw := (RxOrigin.admitRaw_erases msg src ds w h).trans hr
  have pair : runPrefix (RxOrigin.admitRaw msg src ds) w h =
      (.ok (r.value,r.after),(runPrefix (RxOrigin.admitRaw msg src ds) w h).2) :=
    Prod.ext raw rfl
  have receiptEq : (⟨r.value,w,r.after⟩ : RunWitness (Option RxOrigin.Admission))=r := by
    rcases r with ⟨value,before,after⟩
    change before=w at hb
    cases hb
    rfl
  rw [RxOrigin.observeAdmission,runPrefix_receiptObserved,pair]
  simp only [Function.comp_apply,receiptEq]

/-- Exact same-occurrence journal equation, including a later stopped finish.
The admission receipt remains before its finish suffix; no failed World is used. -/
theorem consume_receipt (r : RunWitness (Option RxOrigin.Admission))
    (hb : r.before=w) (hv : r.Valid (RxOrigin.admitSource msg src ds))
    (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    runPrefix (RxOrigin.consume msg src ds) w h =
      let next := (runPrefix (RxOrigin.admitRaw msg src ds) w h).2 ++
        [.receipt (.admission msg src ds r)]
      match r.value with
      | none => (.ok ((),r.after),next)
      | some ctx => runPrefix (finishObserved ctx) r.after next := by
  rw [RxOrigin.consume,RxOrigin.consumeWith,runPrefix_bind,observe_admission r hb hv h]
  cases r.value <;> rfl

end Leanux.Proofs.WG.Queues.RxCredits
