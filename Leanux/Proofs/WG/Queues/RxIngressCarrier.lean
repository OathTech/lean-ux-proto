import Leanux.Proofs.WG.Queues.RxAdmissionCarrier

/-! Actual postallocation queue installation and disposal. Negative errno
returns are source outcomes; a Stop has no returned WGWorld. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

def enqueueDevice (d : Device) (id : SkbId) (pkt : RxPacket) (p : Peer) (ret : Int) (cpu : Int) : Device :=
  { d with
    rxSkbs := d.rxSkbs.insert id ({ pkt with state := .uncrypted })
    peers := (if ret = -ENOSPC then d.peers else d.peers.insert pkt.peer ({ p with rxQueue := p.rxQueue.enqueue id }))
    decryptLastCpu := (if ret = -ENOSPC then d.decryptLastCpu else cpu)
    decryptQueue := (if ret=0 then d.decryptQueue.produce id else d.decryptQueue) }

theorem enqueue_effect {id : SkbId} (hd : w.dev=some d) (hs : d.rxSkbs[id]?=some pkt)
    (hp : d.peers[pkt.peer]?=some p) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient=.ok ((ret,v),ambient')) :
    (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
    ∃ cpu, wgStoreView v={wgStoreView w with dev:=some (enqueueDevice d id pkt p ret cpu)} := by
  simp only [enqueuePerDeviceAndPeerRx,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,aa,hset,q,b,ab,hread,peer,c,ac,hpeer,full,e,ae,hfull,tail⟩ := hr
  have setRun := Packets.setRxSkb_run w ambient d id pkt (fun p => {p with state := .uncrypted}) hd hs
  rw [hset] at setRun
  have ha : a = Packets.update w (fun v => {v with rxSkbs := v.rxSkbs.insert id {pkt with state := .uncrypted}}) :=
    congrArg (fun z => z.1.2) (Except.ok.inj setRun)
  have haa : aa = ambient := congrArg Prod.snd (Except.ok.inj setRun)
  subst aa
  have ad : a.dev = some {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}} := by
    simp [ha,Packets.update,hd]
  obtain ⟨hb,hab,da,hda,hq⟩ := Packets.getRxSkb_current id a b q ambient ab hread
  subst b
  subst ab
  have daeq : da = {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}} :=
    Option.some.inj (hda.symm.trans ad)
  subst da
  have qeq : q = {pkt with state := .uncrypted} := by
    simpa using hq.symm
  subst q
  obtain ⟨hc,hac,dp,hdp,hp'⟩ := getPeer_normal pkt.peer a c peer ambient ac hpeer
  subst c
  subst ac
  have dpeq : dp = {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}} :=
    Option.some.inj (hdp.symm.trans ad)
  subst dp
  have peq : peer = p := by simpa [hp] using hp'.symm
  subst peer
  let af := CounterWindow.record ambient .enqueuePeerQueueFull (decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS))
  change Except.ok ((decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS),a),af) =
      .ok ((full,e),ae) at hfull
  have hfe : full = decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) := (congrArg (fun z => z.1.1) (Except.ok.inj hfull)).symm
  have he : e = a := (congrArg (fun z => z.1.2) (Except.ok.inj hfull)).symm
  have hae : ae = af := (congrArg Prod.snd (Except.ok.inj hfull)).symm
  subst full
  subst e
  rw [hae] at tail
  cases fullEq : decide (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) with
  | true =>
    simp only [fullEq,ite_true,StateT.run_pure] at tail
    have rv : ret = -WG.ENOSPC := (congrArg (fun z => z.1.1) (Except.ok.inj tail)).symm
    have vv : v = a := (congrArg (fun z => z.1.2) (Except.ok.inj tail)).symm
    subst ret
    rw [vv]
    refine ⟨Or.inr (Or.inl rfl),d.decryptLastCpu,?_⟩
    simp [wgStoreView,enqueueDevice,ha,Packets.update,hd,ENOSPC,WG.ENOSPC]
  | false =>
    simp only [fullEq,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,b,bb,hput,dev,c,cc,hdev,cpu,e,ee,hcpu,u,f,ff,hcpuPut,ring,g,gg,hring,tail⟩ := tail
    have hb : b = {a with dev := a.dev.map fun d => {d with peers := d.peers.insert pkt.peer {p with rxQueue := p.rxQueue.enqueue id}}} :=
      congrArg (fun z => z.1.2) (Except.ok.inj hput.symm)
    have hbb : bb = af := congrArg Prod.snd (Except.ok.inj hput.symm)
    subst bb
    let installed := {d with rxSkbs := d.rxSkbs.insert id {pkt with state := .uncrypted}, peers := d.peers.insert pkt.peer {p with rxQueue := p.rxQueue.enqueue id}}
    have getter : ((getDev).run b).run af = .ok ((installed,b),af) := by
      simp [getDev,hb,ad,installed]
    rw [hdev] at getter
    have hdc : dev = installed := congrArg (fun z => z.1.1) (Except.ok.inj getter)
    have hcb : c = b := congrArg (fun z => z.1.2) (Except.ok.inj getter)
    have hcc : cc = af := congrArg Prod.snd (Except.ok.inj getter)
    subst dev
    subst c
    subst cc
    have ce : e = b := by
      simp [cpumaskNextOnlineFrom,branch,AmbientM.branch,StateT.run_bind,
        StateT.run_monadLift] at hcpu
      split at hcpu <;> simp_all
    subst e
    have hf : f = {b with dev := b.dev.map fun d => {d with decryptLastCpu := cpu}} :=
      congrArg (fun z => z.1.2) (Except.ok.inj hcpuPut.symm)
    have hff : ff = ee := congrArg Prod.snd (Except.ok.inj hcpuPut.symm)
    subst ff
    change Except.ok ((d.decryptQueue.full,f),CounterWindow.record ee .enqueueRingFull d.decryptQueue.full) =
      .ok ((ring,g),gg) at hring
    cases hring
    cases ringEq : d.decryptQueue.full with
    | true =>
      simp only [ringEq,ite_true,StateT.run_pure] at tail
      have rv : ret = -WG.EPIPE := (congrArg (fun z => z.1.1) (Except.ok.inj tail)).symm
      have vv : v = f := (congrArg (fun z => z.1.2) (Except.ok.inj tail)).symm
      subst ret
      rw [vv]
      refine ⟨Or.inr (Or.inr rfl),cpu,?_⟩
      simp [wgStoreView,enqueueDevice,hf,hb,ha,Packets.update,hd,ENOSPC,WG.EPIPE]
    | false =>
      simp only [ringEq,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨u,h,hh,hwork,u',i,ii,hinstall,hret⟩ := tail
      have he : h = f := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.queueDeviceWork .decryptWorker) (fun g => g = f))
        f _ u h hh rfl hwork
      subst h
      cases hinstall
      cases hret
      refine ⟨Or.inl rfl,cpu,?_⟩
      simp [wgStoreView,enqueueDevice,hf,hb,ha,Packets.update,hd,ENOSPC]


def rxShape (w : WGWorld) := (w.dev.map (·.ifindex),fun id : SkbId =>
  (w.dev.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))

theorem packet_shape (he : rxShape v=rxShape w) (p : Packet) :
    (packetAt v p).map (fun q => (q.peer,q.keypair)) =
      (packetAt w p).map (fun q => (q.peer,q.keypair)) := by
  have ep := congrArg Prod.fst he
  have hs := congrFun (congrArg Prod.snd he) p.slot
  cases hv : v.dev <;> cases hw : w.dev <;>
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
    have old : ((w.dev.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))=some (p.peer,p.keypair) := by
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
  have old : ((w.dev.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))=some (p.peer,p.keypair) := by
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

theorem enqueue_shape {id : SkbId} (hd : w.dev=some d) (hs : d.rxSkbs[id]?=some pkt) :
    rxShape {w with dev:=some (enqueueDevice d id pkt p ret cpu)}=rxShape w := by
  simp only [rxShape,hd,enqueueDevice,Option.map_some,Option.bind_some]
  congr 1
  funext j
  by_cases he : id=j <;> simp_all [Std.TreeMap.getElem?_insert]

theorem enqueueDevice_keyView {id : SkbId} (hd : w.dev=some d) (hp : d.peers[pkt.peer]?=some p) :
    keyView {w with dev:=some (enqueueDevice d id pkt p ret cpu)}=keyView w := by
  unfold keyView keyWords currentCells
  simp only [hd,enqueueDevice,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases ret=-ENOSPC <;> by_cases pkt.peer=q <;>
    simp_all [Std.TreeMap.getElem?_insert,currentCell]

theorem enqueue_balance {id : SkbId} (hd : w.dev=some d) (hp : d.peers[pkt.peer]?=some p) (o : Owner) :
    balance {w with dev:=some (enqueueDevice d id pkt p ret cpu)} o=balance w o := by
  simp only [balance,resident,hd,enqueueDevice]
  by_cases ret=-ENOSPC <;> by_cases pkt.peer=o.slot <;>
    simp_all [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem enqueue_queues {id : SkbId} (hi : QueueOwners (c::cs) w) (hc : c.phase=.unpublished)
    (hd : w.dev=some d) (hp : d.peers[pkt.peer]?=some p)
    (packet : c.packet=⟨d.ifindex,id⟩) (owner : c.owner=⟨d.ifindex,pkt.peer,p.internalId⟩) :
    QueueOwners ((if ret=-ENOSPC then c else enqueued c)::cs)
      {w with dev:=some (enqueueDevice d id pkt p ret cpu)} := by
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
      simp only [List.filter_cons,hc] at old
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
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx c.packet.slot).run w).run ambient=.ok ((ret,v),ambient')) :
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
  obtain ⟨rets,cpu,hv⟩ := enqueue_effect hd slot hpkt ambient ambient' hr
  let u := {w with dev:=some (enqueueDevice d c.packet.slot pkt p ret cpu)}
  have ku : wgStoreView v=wgStoreView u := hv
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
  · simpa only [ite_eq_left hret] using old
  · by_cases ho : c.owner=o <;> simpa [ite_eq_right hret,demand,charges,enqueued,List.filter_cons,hc,Phase.charged,ho] using old


theorem rxShape_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => rxShape (project w)) a :=
  ha.of_factor (fun store : WGStoreView =>
    (store.dev.map (·.ifindex), fun id : SkbId =>
      (store.dev.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair))) _ (fun _ => rfl)

theorem rxShape_peerGet (pid : PeerId) : SameView rxShape (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  obtain ⟨d,p,hd,hp,pos,hv⟩ := peerGet_loan pid w v ambient ambient' hr
  have dev := congrArg WGStoreView.dev hv
  change v.dev = some _ at dev
  change w.dev = some d at hd
  simp [rxShape,dev,hd]

theorem rxShape_peerPut (pid : Option PeerId) : SameView rxShape (peerPut pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases pid with
  | none =>
    simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,
      StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
      CounterWindow.except_pure] at hr
    rcases hr with ⟨rfl,rfl⟩
    rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
        getPeer,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind,
        StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
      change Except.error _ = Except.ok (((),v),ambient') at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
          getPeer,getDev,hd,hp,invariant,AmbientM.invariant,StateT.run_bind,
          StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
        change Except.error _ = Except.ok (((),v),ambient') at hr
        cases hr
      | some p =>
        have keep := (peerPut_effect pid w v d p ambient ambient' hd hp hr).2.2
        exact congrArg (fun pair => (pair.1,fun id => (pair.2 id).map fun q => (q.peer,q.keypair))) keep

theorem publicationMiddle_shape (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView rxShape (publicationMiddle pid id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  unfold publicationMiddle at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,readAmbient,hg,hr⟩ := hr
  obtain ⟨ha,haA,d,hd,hp⟩ := getPeer_normal pid w a p ambient readAmbient hg
  subst a
  subst readAmbient
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,ite_true] at hr
    cases hr
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,ite_false] at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,b,midway,hs,ht⟩ := hr
    cases slot : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,hd,slot,
        invariant,AmbientM.invariant] at hs
      change Except.error _ = Except.ok ((x,b),midway) at hs
      cases hs
    | some q =>
      have exactSet := Packets.setRxSkb_run w ambient d id q (fun q => {q with state}) hd slot
      rw [hs] at exactSet
      cases exactSet
      cases ht
      simp only [rxShape,Packets.update,hd,Option.map_some,Option.bind_some]
      refine Prod.ext rfl ?_
      funext j
      by_cases he : id = j <;> simp_all [Std.TreeMap.getElem?_insert]

theorem publicationMiddle_keyView (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView keyView (publicationMiddle pid id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  unfold publicationMiddle at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,readAmbient,hg,hr⟩ := hr
  obtain ⟨ha,haA,d,hd,hp⟩ := getPeer_normal pid w a p ambient readAmbient hg
  subst a
  subst readAmbient
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,ite_true] at hr
    cases hr
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,ite_false] at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,b,midway,hs,ht⟩ := hr
    let P : WGWorld → Prop := fun g => g.dev.map (fun d => (d.ifindex,d.peers,d.keypairs)) =
      some (d.ifindex,d.peers,d.keypairs)
    have frame : Hoare (setRxSkb id (fun q => {q with state})) P (fun _ => P) := by
      unfold setRxSkb
      apply hoare_liftSkb
      intro g dev packets hi hg
      simpa [P,hg] using hi
    have hb := (hoare_iff_run_ambient _ _ _).mp frame w ambient x b midway (by simp [P,hd]) hs
    cases hdev : b.dev with
    | none => simp [P,hdev] at hb
    | some db =>
      have fields : db.ifindex = d.ifindex ∧ db.peers = d.peers ∧ db.keypairs = d.keypairs := by
        simpa [P,hdev] using hb
      cases ht
      unfold keyView RxCredits.keyWords RxCredits.currentCells
      simp only [hd,hdev,fields.1,fields.2.1,fields.2.2,Option.map_some,Option.bind_some]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext q
      by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert,currentCell]

theorem publication_preservation (id : SkbId) (state : PacketState)
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run ambient=.ok (((),v),ambient')) :
    baseView v=baseView w ∧ rxShape v=rxShape w ∧ KeyEffect NoPromotion w v := by
  rw [publication_factor] at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,a,aa,hpkt,pid,b,ab,hderef,u,c,ac,hget,u',e,ae,hmid,hput⟩ := hr
  cases u
  cases u'
  have ka := (Packets.getRxSkb_current id w a pkt ambient aa hpkt).1
  subst a
  have kb : b = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun g => g = w))
    w aa pid b ab rfl hderef
  obtain ⟨d,p,hd,hp,pos,hc⟩ := peerGet_loan pid b c ab ac hget
  have hdw : w.dev=some d := kb ▸ hd
  have hm := (ProjectedAction.iff_run_ambient _ _ _).mp
    (publicationMiddle_frame pid id state) c ac () e ae hmid
  have hcdev := congrArg WGStoreView.dev hc
  change c.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at hcdev
  have view : peerView e=peerView (creditWorld w d pid p) :=
    hm.trans (by simp only [peerView,creditWorld,hcdev])
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
  have paid := peerPut_handoff hde hpe count ae ambient' hput
  have basecredit : baseView (creditWorld w d pid p)=baseView w := by
    simp only [baseView,creditWorld,hdw,Option.map_some,Option.bind_some]
    refine Prod.ext rfl ?_
    funext q
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]
  refine ⟨paid.base.trans ((base_of_peerView view).trans basecredit),?_,?_⟩
  · exact ((ProjectedAction.iff_run_ambient _ _ _).mp (rxShape_peerPut (some pid)) e ae () v ambient' hput).trans
      (((ProjectedAction.iff_run_ambient _ _ _).mp (publicationMiddle_shape pid id state) c ac () e ae hmid).trans
        (((ProjectedAction.iff_run_ambient _ _ _).mp (rxShape_peerGet pid) b ab () c ac hget).trans
          (congrArg rxShape kb)))
  · have ke : KeyEffect NoPromotion w e :=
      (keyEffect_of_view (congrArg keyView kb)).trans
        ((keyEffect_of_view ((ProjectedAction.iff_run_ambient _ _ _).mp
          (peerGet_keyView pid) b ab () c ac hget)).trans
          (keyEffect_of_view ((ProjectedAction.iff_run_ambient _ _ _).mp
            (publicationMiddle_keyView pid id state) c ac () e ae hmid)))
    exact ke.trans ((KeyEffects.iff_run_ambient _ _).mp (peerPut_keyEffect (some pid)) e ae () v ambient' hput)

/-- The actual pure IRQ publication preserves all existing charges while
repaying its separate acquired reference. Packet state and NAPI may change. -/
theorem publication_state {id : SkbId} (hi : CarrierState cs loans w)
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run ambient=.ok (((),v),ambient')) : CarrierState cs loans v := by
  obtain ⟨hb,hs,hk⟩ := publication_preservation id state ambient ambient' hr
  exact ⟨inventory_shape hi.inventory hs,queueOwners_base hi.queues hb,
    (by intro o; rw [publication_balances id state w v ambient ambient' hr]; exact hi.funded o),
    rxCompatible_shape hi.keys.1 hs hk,hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩

/-- The normal no-space suffix pays and frees its own unpublished carrier.
The key-put endpoint is extracted from this execution, not assumed separately. -/
theorem discard_state (hi : CarrierState (c::cs) loans w) (hc : c.phase=.unpublished)
    (owner : pkt.peer=c.owner.slot) (ambient ambient' : Ambient)
    (hr : ((discard c.packet.slot pkt).run w).run ambient=.ok (((),v),ambient')) :
    CarrierState cs loans v ∧ packetAt v c.packet=none := by
  obtain ⟨iv,pv,qv,gone⟩ :=
    discard_unpublished_normal hi.inventory hi.funded hi.queues hc owner ambient ambient' hr
  have source := hr
  simp only [discard,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨u,a,aa,hkey,u',b,ab,hpeer,hfree⟩ := source
  cases u
  cases u'
  have ha := keyPut_state _ _ hi ambient aa hkey
  have ke := (KeyEffects.iff_run_ambient _ _).mp
    (peerPut_keyEffect (allowed:=NoPromotion) (some pkt.peer)) a aa () b ab hpeer
  have kb : KeysCompatible b :=
    ⟨rxCompatible_shape ha.keys.1 ((ProjectedAction.iff_run_ambient _ _ _).mp
      (rxShape_peerPut (some pkt.peer)) a aa () b ab hpeer) ke,
      ke.currentsCompatible ha.keys.2 (by intro p k h; exact h.elim)⟩
  exact ⟨⟨iv,qv,pv,freeRx_keys _ kb ab ambient' hfree⟩,gone⟩

def finishAfter (ctx : RxOrigin.Admission) (ret : Int) : WG.M Unit := do
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
    (ambient ambient' : Ambient)
    (hr : ((finishSource ctx).run w).run ambient=.ok (((),v),ambient')) :
    ∃ ret a aAmbient, ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient=.ok ((ret,a),aAmbient) ∧
      ((finishAfter ctx ret).run a).run aAmbient=.ok (((),v),ambient') ∧
      (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      (if ret=-ENOSPC then CarrierState cs loans v ∧ packetAt v c.packet=none
       else CarrierState (enqueued c::cs) loans v) := by
  have whole := hr
  rw [finish_factor] at hr
  obtain ⟨ret,a,aa,he,ht⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using hr)
  obtain ⟨choices,ha⟩ := enqueue_state hi hc hs owner ambient aa (by simpa [slot] using he)
  refine ⟨ret,a,aa,he,ht,choices,?_⟩
  rcases choices with rfl | rfl | rfl
  · have vv : v = a := by
      simp [finishAfter,WG.orM,branch,AmbientM.branch,EPIPE,
        StateT.run_bind,StateT.run_monadLift] at ht
      exact ht.1.symm
    have state : CarrierState (enqueued c::cs) loans a := by simpa [ENOSPC] using ha
    simpa [ENOSPC,vv] using state
  · have run : ((discard c.packet.slot ctx.packet).run a).run (enospcDecisions aa)=.ok (((),v),ambient') := by
      simpa [slot] using (finish_enospc ctx ambient aa he).symm.trans whole
    have initial : CarrierState (c::cs) loans a := by simpa using ha
    simpa using discard_state initial hc owner (enospcDecisions aa) ambient' run
  · simp only [finishAfter,MaterialOrigin.bind_ok_ambient] at ht
    obtain ⟨decision,z,az,hbranch,ht⟩ := ht
    change Except.ok ((true,a),CounterWindow.record aa .dataEpipe true) =
      .ok ((decision,z),az) at hbranch
    have dv : decision = true := (congrArg (fun z => z.1.1) (Except.ok.inj hbranch)).symm
    have zv : z = a := (congrArg (fun z => z.1.2) (Except.ok.inj hbranch)).symm
    have av : az = CounterWindow.record aa .dataEpipe true := (congrArg Prod.snd (Except.ok.inj hbranch)).symm
    subst decision
    subst z
    rw [av] at ht
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at ht
    obtain ⟨u,b,bb,hpublish,tail⟩ := ht
    cases u
    have hb := publication_state
      (show CarrierState (enqueued c::cs) loans a from by simpa [ENOSPC,EPIPE] using ha)
      (CounterWindow.record aa .dataEpipe true) bb hpublish
    have vv : v = b := by
      simp [WG.orM,branch,AmbientM.branch,EPIPE,StateT.run_bind,StateT.run_monadLift] at tail
      exact tail.1.symm
    simpa [ENOSPC,EPIPE,vv] using hb

theorem admitted_packet (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((some ctx,v),ambient'))
    (hp : packetAt v ⟨epoch,ctx.slot⟩=some pkt) : pkt=ctx.packet := by
  obtain ⟨entry,a,aa,b,ab,c,ac,peer,d,ad,e,ae,_,_,_,_,_,_,hn⟩ :=
    RxOrigin.admission_execution _ _ _ _ _ _ ambient ambient' hr
  obtain ⟨dev,hd,slot,after,_,_⟩ :=
    RxOrigin.allocation_record ctx.packet ⟨ctx.slot,e,v,ae,ambient'⟩ hn
  change e.dev=some dev at hd
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
    (src : SkbSource) (ds : Nat) (w v : WGWorld) (ambient ambient' : Ambient)
    (r : WGRunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before=w ∧ r.ambientBefore=ambient ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after=v ∧ r.ambientAfter=ambient' ∧ CarrierState cs loans v
  | some ctx => ∃ o,
      let c : Carrier := ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩
      CarrierState (c::cs) loans r.after ∧ o.slot=ctx.packet.peer ∧
      KeyWord ctx.packet.keypair ctx.packet.peer r.after ∧
      RxOrigin.Admitted msg src ds ctx w r.after ambient r.ambientAfter ∧
      ∃ ret a aAmbient, ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=.ok ((ret,a),aAmbient) ∧
        ((finishAfter ctx ret).run a).run aAmbient=.ok (((),v),ambient') ∧
        (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        (if ret=-ENOSPC then CarrierState cs loans v ∧ packetAt v c.packet=none
         else CarrierState (enqueued c::cs) loans v)

theorem consume_normal (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (ambient ambient' : Ambient)
    (hr : ((consumeData msg src ds).run w).run ambient=.ok (((),v),ambient')) :
    ∃ r, Consumption cs loans msg src ds w v ambient ambient' r := by
  rw [←RxOrigin.consumeSource_eq] at hr
  unfold RxOrigin.consumeSource RxOrigin.consumeWith at hr
  obtain ⟨result,a,aa,hfront,htail⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using hr)
  refine ⟨⟨result,w,a,ambient,aa⟩,rfl,rfl,hfront,?_⟩
  cases result with
  | none =>
    have he : a=v ∧ aa=ambient' := by simpa using htail
    rcases he with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,admitted_none hi ambient _ hfront⟩
  | some ctx =>
    obtain ⟨o,ha,owner,word,admitted⟩ := admitted_state hi hf ambient aa hfront
    obtain ⟨_,pkt,hp,_⟩ := ha.inventory.present
      ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ (by simp)
    have he : pkt=ctx.packet := admitted_packet ambient aa hfront hp
    subst pkt
    exact ⟨o,ha,owner,word,admitted,finish_state ctx ha rfl rfl hp owner.symm aa ambient' htail⟩

def finishObserved (ctx : RxOrigin.Admission) : RxOrigin.Journal Unit :=
  RxOrigin.finishWith (fun k b => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (keypairPutPrefix k b))
    (fun p => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (peerPutMixed p))
    (fun id => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (enqueuePerDeviceAndPeerRxPrefix id))
    (fun id => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (enqueuePerPeerRxNativePrefix id .dead))
    (fun id => focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (freeRxSkbPrefix id)) liftWGPrefix ctx

/-- The admission receipt is appended to this execution's actual front output.
Its captured WG and Ambient endpoints are the witness used by conservation. -/
theorem observe_admission (r : WGRunWitness (Option RxOrigin.Admission))
    (hb : r.before=w) (hab : r.ambientBefore=ambient) (hv : r.Valid (RxOrigin.admitSource msg src ds))
    (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    runWGPrefix (RxOrigin.observeAdmission msg src ds) w ambient h =
      (.ok ((r.value,r.after),r.ambientAfter),
        (runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2 ++
          [.receipt (.admission msg src ds r)]) := by
  have hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((r.value,r.after),r.ambientAfter) := by
    simpa [WGRunWitness.Valid,hb,hab] using hv
  have raw := (RxOrigin.admitRaw_erases msg src ds w ambient h).trans hr
  have pair : runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h =
      (.ok ((r.value,r.after),r.ambientAfter),(runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2) :=
    Prod.ext raw rfl
  have receiptEq : (⟨r.value,w,r.after,ambient,r.ambientAfter⟩ : WGRunWitness (Option RxOrigin.Admission))=r := by
    rcases r with ⟨value,before,after,ambientBefore,ambientAfter⟩
    change before=w at hb
    change ambientBefore=ambient at hab
    cases hb
    cases hab
    rfl
  rw [RxOrigin.observeAdmission,runWGPrefix_receiptWGObserved,pair]
  simp only [Function.comp_apply,receiptEq]

/-- Exact same-occurrence journal equation, including a later stopped finish.
The admission receipt remains before its finish suffix; no failed state is used. -/
theorem consume_receipt (r : WGRunWitness (Option RxOrigin.Admission))
    (hb : r.before=w) (hab : r.ambientBefore=ambient) (hv : r.Valid (RxOrigin.admitSource msg src ds))
    (h : List (MaterialOrigin.Event RxOrigin.Receipt)) :
    runWGPrefix (RxOrigin.consume msg src ds) w ambient h =
      let next := (runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2 ++
        [.receipt (.admission msg src ds r)]
      match r.value with
      | none => (.ok (((),r.after),r.ambientAfter),next)
      | some ctx => runWGPrefix (finishObserved ctx) r.after r.ambientAfter next := by
  change runStatePrefix _ _ _ _ = _
  rw [RxOrigin.consume,RxOrigin.consumeWith,runStatePrefix_bind]
  have observed := observe_admission r hb hab hv h
  change runStatePrefix _ _ _ _ = _ at observed
  rw [observed]
  cases r.value <;> rfl

end Leanux.Proofs.WG.Queues.RxCredits
