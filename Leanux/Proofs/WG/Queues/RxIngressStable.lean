import Leanux.Proofs.WG.Queues.RxIngressCarrier

/-! Stable RX boundaries relate the logical ring to the same carrier ledger.
Physical stale slots remain governed by the separate initialized ring model.
A cold nonempty peer queue must have an uncrypted head; ready tails can wait
behind that head. None of these definitions asserts initialized reachability. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

def uncrypted (cs : Ledger) (w : World) : List Packet :=
  (cs.filter fun c => (packetAt w c.packet).any (fun p => p.state == .uncrypted)).map (·.packet)

structure StableRx (cs : Ledger) (w : World) : Prop where
  queued : ∀ c ∈ cs, c.phase=.queued
  ring : ∀ d, w.k.wg=some d →
    (d.decryptQueue.items.map fun id => Packet.mk d.ifindex id).Perm (uncrypted cs w)
  cold : ∀ (d : Device) (pid : PeerId) (p : Peer) (id : SkbId), w.k.wg=some d → d.peers[pid]?=some p →
    p.napiScheduled=false → p.rxQueue.all.head?=some id →
    ∃ pkt : RxPacket, d.rxSkbs[id]?=some pkt ∧ pkt.state=.uncrypted

theorem uncrypted_member (hc : c∈cs) (hp : packetAt w c.packet=some p)
    (hs : p.state=.uncrypted) : c.packet∈uncrypted cs w := by
  apply List.mem_map.mpr
  exact ⟨c,List.mem_filter.mpr ⟨hc,by simp [hp,hs]; rfl⟩,rfl⟩

/-- Initialized physical geometry makes an empty head imply an empty logical
ring, including size zero. An arbitrary malformed PtrRing would not suffice. -/
theorem ring_empty_items (hr : RxRing.Refines (PtrRing.init n) h r)
    (he : r.empty=true) : r.items=[] := by
  by_cases hn : n=0
  · subst n
    obtain ⟨commands,hcommands⟩ := hr
    rw [Ring.Journal.run_zero _ (by rfl)] at hcommands
    have same : r=PtrRing.init 0 := (congrArg Prod.snd hcommands).symm
    rw [same]
    rfl
  · obtain ⟨t,retired,stale,live,hb,eq,_,_⟩ := hr.initialized.1 (by omega)
    subst r
    rw [Ring.items hb]
    have hp := Ring.peek (batch:=(PtrRing.init (α:=SkbId) n).batch) hb
    have empty : live.head?.isNone=true := by simpa [PtrRing.empty,hp] using he
    cases live <;> simp_all

/-- A guarded successful production extends logical contents exactly once.
This derives from the existing physical journal even for a zero-sized initial ring. -/
theorem ring_produce_items (hr : RxRing.Refines (PtrRing.init n) h r)
    (hf : r.full=false) (id : SkbId) : (r.produce id).items=r.items++[id] := by
  have old := hr.initialized.2.1
  have next := (hr.step (.offer id)).initialized.2.1
  simp only [Ring.Journal.step,tryProduce,hf,Bool.false_eq_true,↓reduceIte] at next
  simp only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,List.append_nil] at next old
  rw [old,List.append_assoc] at next
  exact (List.append_cancel_left next).symm

/-- At a stable boundary, the actual empty physical ring and absence of NAPI
work force the same funded carrier ledger and the complete RX store to be empty. -/
theorem stable_drained (hi : CarrierState cs loans w) (hs : StableRx cs w)
    (physical : RxRing.Inv epoch (PtrRing.init n) h w)
    (empty : ∀ d, w.k.wg=some d → d.decryptQueue.empty=true)
    (cold : ∀ (d : Device) (pid : PeerId) (p : Peer), w.k.wg=some d → d.peers[pid]?=some p → p.napiScheduled=false) :
    cs=[] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket), w.k.wg=some d → d.rxSkbs[id]?≠some pkt := by
  have nil : cs=[] := by
    apply Classical.byContradiction
    intro nonempty
    obtain ⟨c,rest,eq⟩ := List.exists_cons_of_ne_nil nonempty
    subst cs
    have phase := hs.queued c (by simp)
    have demand : 0<demand (c::rest) loans c.owner := by
      simp [demand,charges,phase,Phase.charged]; omega
    obtain ⟨p,hp,_⟩ := protected_resident hi.funded demand
    obtain ⟨d,hd,epoch,hpeer,stamp⟩ := resident_fields hp
    have packet : c.packet=⟨d.ifindex,c.packet.slot⟩ := by
      have ep := (hi.inventory.present c (by simp)).1
      cases he : c.packet
      simp_all [Packet.mk.injEq]
    have owner : c.owner=⟨d.ifindex,c.owner.slot,p.internalId⟩ := by
      cases he : c.owner
      simp_all [Owner.mk.injEq]
    have count := hi.queues d c.owner.slot p c.packet.slot hd hpeer
    have positive : 0<p.rxQueue.all.count c.packet.slot := by
      have test : (c.packet == ⟨d.ifindex,c.packet.slot⟩ &&
          c.owner == ⟨d.ifindex,c.owner.slot,p.internalId⟩ && c.phase == .queued)=true := by
        simp only [Bool.and_eq_true,beq_iff_eq]
        exact ⟨⟨packet,owner⟩,phase⟩
      simp only [List.filter_cons,test,↓reduceIte,List.length_cons] at count
      omega
    have qne : p.rxQueue.all≠[] := by intro qnil; simp [qnil] at positive
    obtain ⟨id,tail,hqueue⟩ := List.exists_cons_of_ne_nil qne
    obtain ⟨pkt,hpkt,hstate⟩ := hs.cold d c.owner.slot p id hd hpeer (cold d _ p hd hpeer)
      (by simp [hqueue])
    obtain ⟨x,hx,hxpacket⟩ := hi.inventory.complete d id pkt hd hpkt
    have stored : packetAt w x.packet=some pkt := by simp [hxpacket,packetAt,hd,hpkt]
    have mem := uncrypted_member hx stored hstate
    obtain ⟨ring,href,hcell⟩ := physical
    have ringEq : ring=d.decryptQueue := by simpa [RxRing.cell,hd] using congrArg (Option.map Prod.snd) hcell.symm
    have noItems : d.decryptQueue.items=[] := ring_empty_items (ringEq ▸ href) (empty d hd)
    have perm := hs.ring d hd
    rw [noItems,List.map_nil] at perm
    have noUncrypted : uncrypted (c::rest) w=[] := (List.Perm.nil_eq perm).symm
    simp [noUncrypted] at mem
  refine ⟨nil,?_⟩
  intro d id pkt hd hp
  obtain ⟨c,hc,_⟩ := hi.inventory.complete d id pkt hd hp
  simp [nil] at hc


/-- Only fields used by stable RX boundaries. Reference counts and key state
may change without changing this view. -/
def stableView (w : World) :=
  (RxRing.cell w, rxView w, fun pid : PeerId =>
    (w.k.wg.bind fun d => d.peers[pid]?).map fun p => (p.rxQueue,p.napiScheduled))

theorem StableRx.view (hs : StableRx cs w) (hv : stableView v=stableView w) : StableRx cs v := by
  have ring : RxRing.cell v=RxRing.cell w := congrArg Prod.fst hv
  have rx : rxView v=rxView w := congrArg (fun x => x.2.1) hv
  have peers : (fun (pid : PeerId) => (v.k.wg.bind fun d => d.peers[pid]?).map fun (p : Peer) => (p.rxQueue,p.napiScheduled)) =
      (fun (pid : PeerId) => (w.k.wg.bind fun d => d.peers[pid]?).map fun (p : Peer) => (p.rxQueue,p.napiScheduled)) := congrArg (fun x => x.2.2) hv
  have packets : ∀p,packetAt v p=packetAt w p := fun p => by
    have epoch := congrArg Prod.fst rx
    have slots := congrFun (congrArg Prod.snd rx) p.slot
    cases h₁:v.k.wg <;> cases h₂:w.k.wg <;> simp_all [rxView,packetAt]
  refine ⟨hs.queued,?_,?_⟩
  · intro d hd
    have old : ∃e,w.k.wg=some e ∧ e.ifindex=d.ifindex ∧ e.decryptQueue=d.decryptQueue := by
      cases hw:w.k.wg <;> simp_all [stableView,RxRing.cell]
    obtain ⟨e,he,ep,hq⟩ := old
    have perm := hs.ring e he
    simpa [ep,hq,uncrypted,packets] using perm
  · intro d pid p id hd hp cold head
    have old : ∃e q,w.k.wg=some e ∧ e.peers[pid]?=some q ∧ q.rxQueue=p.rxQueue ∧ q.napiScheduled=p.napiScheduled := by
      have eq := congrFun peers pid
      simp only [stableView,hd,Option.bind_some,hp,Option.map_some] at eq
      obtain ⟨q,hq,hfields⟩ := Option.map_eq_some_iff.mp eq.symm
      obtain ⟨e,he,hep⟩ := Option.bind_eq_some_iff.mp hq
      exact ⟨e,q,he,hep,(congrArg Prod.fst hfields),(congrArg Prod.snd hfields)⟩
    obtain ⟨e,q,he,hq,queue,napi⟩ := old
    obtain ⟨pkt,hpkt,state⟩ := hs.cold e pid q id he hq (napi.trans cold) (queue ▸ head)
    have slots := congrFun (congrArg Prod.snd rx) id
    exact ⟨pkt,by simpa [rxView,hd,he,hpkt] using slots,state⟩

theorem stableView_kernel (ha : SameKernel a) : SameView stableView a := by
  intro w x v hr
  unfold stableView RxRing.cell rxView
  rw [ha w x v hr]

theorem stable_peerGetMaybeZero (id : Option PeerId) : SameView stableView (peerGetMaybeZero id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGetMaybeZero,requireNotPending,getPeer,getDev,getK,setPeer,modifyDev,
    modifyK,refcountIncNotZero,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView]
  all_goals subst_vars
  all_goals simp_all
  all_goals funext pid
  all_goals simp only [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all

theorem stable_ownerStore (owner : IndexOwner) (word : Option PeerId) : SameView stableView (owner.setPeerWord word) := by
  apply SameView.of_wp
  intro s
  cases owner <;> mvcgen [IndexOwner.setPeerWord,getPeer,getKeypair,getDev,getK,setPeer,setKeypair,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView]
  all_goals subst_vars
  all_goals simp_all
  all_goals funext pid
  all_goals simp only [Std.TreeMap.getElem?_insert]
  all_goals split <;> simp_all

theorem stable_acquireOwner (owner : IndexOwner) : SameView stableView (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  exact (stableView_kernel (indexOwner_peerWord_sameKernel owner)).bind fun word =>
    (stable_peerGetMaybeZero word).bind fun result =>
      (stable_ownerStore owner result).bind fun _ => SameView.pure _ _

theorem stable_indexLookup (kinds : List IndexKind) (index : Nat) : SameView stableView (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  apply SameView.of_wp
  intro s
  have ha := fun owner => (stable_acquireOwner owner).wp (fun t => t=s)
  have hb := (stableView_kernel (Framing.indexBucket_sameKernel index)).wp (fun t => t=s)
  mvcgen [Affiliation.indexLookupSource,ha,hb,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜stableView w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView]

theorem stable_keypairGet (id : Option KeypairId) : SameView stableView (keypairGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountIncNotZero,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView]

theorem stable_keypairPut (id : Option KeypairId) (now : Bool) : SameView stableView (keypairPut id now) := by
  apply SameView.of_wp
  intro s
  simp only [keypairPut,indexRemove_eq]
  have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v=k)
  mvcgen [hd,indexUnhash,getKeypair,getDev,getK,setKeypair,modifyDev,modifyK,
    refcountDecAndTest,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView,Option.map_map,Option.bind_map,Function.comp_def]
  all_goals subst_vars
  all_goals simp_all


theorem StableRx.peerKernel (hs : StableRx cs w) (hd : w.k.wg=some d)
    (peers : Std.TreeMap PeerId Peer compare)
    (back : ∀(pid : PeerId) (p : Peer),peers[pid]?=some p → ∃q : Peer,d.peers[pid]?=some q ∧
      q.rxQueue=p.rxQueue ∧ q.napiScheduled=p.napiScheduled) :
    StableRx cs {w with k:={w.k with wg:=some {d with peers}}} := by
  refine ⟨hs.queued,?_,?_⟩
  · intro out hout
    have he : out={d with peers} := Option.some.inj hout.symm
    subst out
    simpa [uncrypted,packetAt,hd] using hs.ring d hd
  · intro out pid p id hout hp cold head
    have he : out={d with peers} := Option.some.inj hout.symm
    subst out
    obtain ⟨q,hq,queue,napi⟩ := back pid p hp
    exact hs.cold d pid q id hd hq (napi.trans cold) (queue ▸ head)

theorem stable_payment_effect (hd : w.k.wg=some d) (hp : d.peers[pid]?=some p)
    (hr : (peerPut (some pid)).run w=.ok ((),v)) :
    stableView v=stableView {w with k:=paymentKernel w.k d pid p} := by
  have hg := PeerBorrow.getPeer_known w.k d pid p hd hp
  have hs : ⦃fun z => ⌜z.k=w.k⌝⦄ peerPut (some pid)
      ⦃⇓? _ z => ⌜stableView z=stableView {w with k:=paymentKernel w.k d pid p}⌝⦄ := by
    simp only [peerPut,indexRemove_eq]
    mvcgen [hg,requireNotPending,getDev,getK,setPeer,modifyDev,modifyK,refcountDecAndTest,
      branch,branchCmp,indexUnhash,retirePeerUnits,invariant,unsupported]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [stableView,RxRing.cell,rxView,paymentKernel,Option.map_map,Option.bind_map,Function.comp_def]
    all_goals subst_vars
    all_goals dsimp only
    all_goals simp [funext_iff,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase]
    all_goals intro q; by_cases h : pid=q <;> simp [h]
  exact (hoare_iff_triple _ _ _).mpr hs w () v rfl hr

theorem StableRx.put (hs : StableRx cs w)
    (hr : (peerPut pid).run w=.ok ((),v)) : StableRx cs v := by
  cases pid with
  | none =>
    have hv : v=CounterWindow.record w .peerPutNull true := by simpa [peerPut] using hr.symm
    apply hs.view
    rw [hv]
    rfl
  | some pid =>
    obtain ⟨d,p,hd,hp⟩ : ∃d p,w.k.wg=some d ∧ d.peers[pid]?=some p := by
      cases hd:w.k.wg with
      | none => simp [peerPut,requireNotPending,getPeer,getDev,getK,hd,branch,invariant] at hr
      | some d =>
        cases hp:d.peers[pid]? with
        | none => simp [peerPut,requireNotPending,getPeer,getDev,getK,hd,hp,branch,invariant] at hr
        | some p => exact ⟨d,p,rfl,hp⟩
    apply StableRx.view (w:={w with k:=paymentKernel w.k d pid p}) _ (stable_payment_effect hd hp hr)
    apply hs.peerKernel hd _
    intro q out hout
    by_cases h:p.refcount=1
    · simp only [h,↓reduceIte,Std.TreeMap.getElem?_erase] at hout
      split at hout
      · contradiction
      · exact ⟨out,hout,rfl,rfl⟩
    · simp only [h,↓reduceIte,Std.TreeMap.getElem?_insert] at hout
      split at hout
      · have he : out={p with refcount:=p.refcount-1} := Option.some.inj hout.symm
        subst out
        rename_i eq
        have same : pid=q := by simpa using eq
        subst q
        exact ⟨p,hp,rfl,rfl⟩
      · exact ⟨out,hout,rfl,rfl⟩


theorem uncrypted_eq (he : ∀c∈cs,packetAt v c.packet=packetAt w c.packet) :
    uncrypted cs v=uncrypted cs w := by
  unfold uncrypted
  congr 1
  apply List.filter_congr
  intro c hc
  rw [he c hc]

theorem StableRx.allocate (hs : StableRx cs w) (hi : Inventory cs w)
    (hd : w.k.wg=some d) (fresh : d.rxSkbs[d.nextSkb]?=none) (pkt : RxPacket) :
    StableRx cs (Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1}) := by
  let v := Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1}
  have keeps : ∀c∈cs,packetAt v c.packet=packetAt w c.packet := by
    intro c hc
    obtain ⟨ep,p,hp,owner⟩ := hi.present c hc
    have epoch : d.ifindex=c.packet.epoch := by
      by_cases h:d.ifindex=c.packet.epoch
      · exact h
      · simp [packetAt,hd,h] at hp
    have ne : d.nextSkb≠c.packet.slot := by
      intro h
      simp [packetAt,hd,epoch,←h,fresh] at hp
    simp [v,Packets.update,packetAt,hd,epoch,Std.TreeMap.getElem?_insert,ne]
  refine ⟨hs.queued,?_,?_⟩
  · intro out hout
    have eq : out={d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1} := by simpa [Packets.update,hd] using hout.symm
    subst out
    rw [uncrypted_eq keeps]
    exact hs.ring d hd
  · intro out pid p id hout hp cold head
    have eq : out={d with rxSkbs:=d.rxSkbs.insert d.nextSkb pkt,nextSkb:=d.nextSkb+1} := by simpa [Packets.update,hd] using hout.symm
    subst out
    obtain ⟨q,hq,state⟩ := hs.cold d pid p id hd hp cold head
    have ne : d.nextSkb≠id := by intro h; simp [←h,fresh] at hq
    exact ⟨q,by simpa [Std.TreeMap.getElem?_insert,ne] using hq,state⟩

theorem stable_receiveKey (entry : Option (IndexOwner × PeerId)) :
    SameView stableView (Affiliation.receiveKeyAcquire entry) := by
  cases entry with
  | none =>
    simpa [Affiliation.receiveKeyAcquire] using
      (stableView_kernel keypairGetCurrent_sameKernel).bind (fun _ => SameView.pure _ _)
  | some e =>
    rcases e with ⟨owner,pid⟩
    cases owner
    · intro w r v hr
      cases hr
    · simpa [Affiliation.receiveKeyAcquire] using
        (stable_keypairGet (some _)).bind (fun _ => SameView.pure _ _)

theorem admitted_stable_front (hs : StableRx cs w) (hi : Inventory cs w) (hf : Packets.Inv w)
    (hr : (RxOrigin.admitSource msg src ds).run w=.ok (some ctx,v)) : StableRx cs v := by
  obtain ⟨entry,a,b,c,peer,d,e,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v hr
  have vb := (stable_receiveKey entry a _ b hk).trans (stable_indexLookup [.keypair] (u32le msg 4) w _ a hl)
  have kc := sameKernel_branch .dataNoKeypair false b false c hno
  have kd := (getPeer_normal ctx.packet.peer c d peer hp).1
  have ke := sameKernel_branch .dataPeerDead peer.isDead d false e hd
  have eb : e.k=b.k := ke.trans ((congrArg World.k kd).trans kc)
  have ve : stableView e=stableView w := by
    simpa [stableView,RxRing.cell,rxView,eb] using vb
  have ie : Inventory cs e := inventory_view hi (congrArg (fun x => x.2.1) ve)
  have packets := (receiveKey_packets entry a _ b hk).trans (indexLookup_packets [.keypair] (u32le msg 4) w entry a hl)
  have pe : Packets.snapshot e=Packets.snapshot w := by simpa only [Packets.snapshot,eb] using packets
  have fe : Packets.Inv e := by simpa only [Packets.Inv,pe] using hf
  obtain ⟨dev,hdev,slot,after,stored⟩ := RxOrigin.allocation_record ctx.packet ⟨ctx.slot,e,v⟩ hn
  change e.k.wg=some dev at hdev
  change v=Packets.update e _ at after
  rw [after]
  simpa [Packets.update,hdev] using (hs.view ve).allocate ie hdev (Packets.allocation_slots_empty e dev hdev fe).2 ctx.packet


theorem StableRx.kernel (hs : StableRx cs w) (hk : v.k=w.k) : StableRx cs v :=
  hs.view (by unfold stableView RxRing.cell rxView; rw [hk])

theorem stable_enqueue {id : SkbId} {pkt : RxPacket} (hs : StableRx cs w) (hd : w.k.wg=some d)
    (hp : d.peers[pkt.peer]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (state : pkt.state=.uncrypted) (cp : c.packet=⟨d.ifindex,id⟩)
    (physical : RxRing.Refines (PtrRing.init n) h d.decryptQueue)
    (hr : (enqueuePerDeviceAndPeerRx id).run w=.ok (ret,v)) :
    if ret=0 then StableRx (enqueued c::cs) v else StableRx cs v := by
  obtain ⟨outcomes,cpu,hv⟩ := enqueue_effect hd hpacket hp hr
  let v0 : World := {w with k:={w.k with wg:=some (enqueueDevice d id pkt p ret cpu)}}
  have same : {pkt with state:=PacketState.uncrypted}=pkt := by cases pkt; simp_all
  have rx : rxView v0=rxView w := by
    simp only [rxView,v0,hd,enqueueDevice,Option.map_some,Option.bind_some]
    congr 1
    funext j
    by_cases he : id=j
    · subst j
      simp [hpacket,same]
    · simp [Std.TreeMap.getElem?_insert,he]
  have packets : ∀x : Carrier,packetAt v0 x.packet=packetAt w x.packet := by
    intro x
    by_cases he : d.ifindex=x.packet.epoch
    all_goals by_cases hx : id=x.packet.slot
    all_goals simp_all [packetAt,v0,hd,enqueueDevice,Std.TreeMap.getElem?_insert,same]
  have cold : ∀(out : Device) (pid : PeerId) (q : Peer) (sid : SkbId),v0.k.wg=some out → out.peers[pid]?=some q →
      q.napiScheduled=false → q.rxQueue.all.head?=some sid →
      ∃stored : RxPacket,out.rxSkbs[sid]?=some stored ∧ stored.state=.uncrypted := by
    intro out pid q sid hout hq hnapi hhead
    have eq : out=enqueueDevice d id pkt p ret cpu := Option.some.inj hout.symm
    subst out
    have store : ∀sid : SkbId,(enqueueDevice d id pkt p ret cpu).rxSkbs[sid]?=d.rxSkbs[sid]? := by
      intro j
      by_cases he:id=j <;> simp_all [enqueueDevice,Std.TreeMap.getElem?_insert,same]
    by_cases space : ret=-ENOSPC
    · obtain ⟨stored,hstored,hstate⟩ := hs.cold d pid q sid hd (by simpa [enqueueDevice,space] using hq) hnapi hhead
      exact ⟨stored,(store sid).trans hstored,hstate⟩
    · by_cases same : pkt.peer=pid
      · subst pid
        have eq : q={p with rxQueue:=p.rxQueue.enqueue id} := by simpa [enqueueDevice,space] using hq.symm
        subst q
        have queue : (p.rxQueue.enqueue id).all=p.rxQueue.all++[id] := by simp [PrevQueue.all,PrevQueue.enqueue,List.append_assoc]
        cases hlist:p.rxQueue.all with
        | nil =>
          have ids : id=sid := by simpa [queue,hlist] using hhead
          subst sid
          exact ⟨pkt,(store id).trans hpacket,state⟩
        | cons first rest =>
          have head : p.rxQueue.all.head?=some sid := by simpa [queue,hlist] using hhead
          obtain ⟨stored,hstored,hstate⟩ := hs.cold d pkt.peer p sid hd hp hnapi head
          exact ⟨stored,(store sid).trans hstored,hstate⟩
      · obtain ⟨stored,hstored,hstate⟩ := hs.cold d pid q sid hd
          (by simpa [enqueueDevice,space,Std.TreeMap.getElem?_insert,same] using hq) hnapi hhead
        exact ⟨stored,(store sid).trans hstored,hstate⟩
  have unchanged : uncrypted cs v0=uncrypted cs w := uncrypted_eq (fun c _ => packets c)
  by_cases zero : ret=0
  · simp only [zero,↓reduceIte]
    apply StableRx.kernel (v:=v) (w:=v0) _ hv
    refine ⟨?_,?_,cold⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hs.queued x hx
    · intro out hout
      have eq : out=enqueueDevice d id pkt p ret cpu := Option.some.inj hout.symm
      subst out
      have free : d.decryptQueue.full=false := RxRing.enqueue_free (deviceIndex:=d.ifindex) (r:=d.decryptQueue) id (by simp [RxRing.cell,hd]) (zero ▸ hr)
      have contents := ring_produce_items physical free id
      have newlist : uncrypted (enqueued c::cs) v0=c.packet::uncrypted cs w := by
        have hc : packetAt v0 c.packet=some pkt := (packets c).trans (by simp [enqueued,cp,packetAt,hd,hpacket])
        have test : ((PacketState.uncrypted)==PacketState.uncrypted)=true := rfl
        simpa only [uncrypted,enqueued,List.filter_cons,hc,Option.any_some,state,test,ite_true,List.map_cons] using congrArg (List.cons c.packet) unchanged
      rw [newlist]
      simp only [enqueueDevice,zero,↓reduceIte,contents,List.map_append,List.map_cons,List.map_nil]
      have last : (uncrypted cs w++[Packet.mk d.ifindex id]).Perm (c.packet::uncrypted cs w) := by
        rw [cp]
        exact List.perm_append_comm
      exact ((hs.ring d hd).append_right [⟨d.ifindex,id⟩]).trans last
  · simp only [zero,↓reduceIte]
    apply StableRx.kernel (v:=v) (w:=v0) _ hv
    refine ⟨hs.queued,?_,cold⟩
    intro out hout
    have eq : out=enqueueDevice d id pkt p ret cpu := Option.some.inj hout.symm
    subst out
    rw [unchanged]
    simpa [enqueueDevice,zero] using hs.ring d hd


theorem admitted_none_stable (hs : StableRx cs w)
    (hr : (RxOrigin.admitSource msg src ds).run w=.ok (none,v)) : StableRx cs v := by
  rw [RxOrigin.admitSource_factor] at hr
  obtain ⟨entry,a,hl,acquired,b,hk,noKey,c,hn,rest⟩ := (by simpa only [MaterialOrigin.bind_ok] using hr)
  rcases acquired with ⟨kp,pid⟩
  have front := hs.view ((stable_receiveKey entry a _ b hk).trans (stable_indexLookup [.keypair] (u32le msg 4) w _ a hl))
  have fc := front.kernel (sameKernel_branch .dataNoKeypair kp.isNone b noKey c hn)
  cases noKey with
  | true =>
    simp only [↓reduceIte,MaterialOrigin.bind_ok] at rest
    obtain ⟨u,z,hpay,he⟩ := rest
    cases u
    have zv : z=v := by simpa using he
    subst z
    exact fc.put hpay
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
          exact (fe.view (stable_keypairPut (some kid) false e () f hkey)).put hpay
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,MaterialOrigin.bind_ok] at rest
          obtain ⟨slot,z,ha,bad⟩ := rest
          simp at bad


theorem queued_head {id : SkbId} (hq : QueueOwners cs w) (hd : w.k.wg=some d) (hp : d.peers[pid]?=some p)
    (head : p.rxQueue.all.head?=some id) : ∃c∈cs,c.packet=⟨d.ifindex,id⟩ ∧
      c.owner=⟨d.ifindex,pid,p.internalId⟩ ∧ c.phase=.queued := by
  have count := hq d pid p id hd hp
  have positive : 0<p.rxQueue.all.count id := by
    cases h:p.rxQueue.all with
    | nil => simp [h] at head
    | cons first rest =>
      have he : first=id := by simpa [h] using head
      subst first
      simp [h]
  have nonempty : (cs.filter fun c => c.packet==⟨d.ifindex,id⟩ &&
      c.owner==⟨d.ifindex,pid,p.internalId⟩ && c.phase==.queued)≠[] := by
    intro he
    rw [he] at count
    simp only [List.length_nil] at count
    omega
  obtain ⟨c,rest,eq⟩ := List.exists_cons_of_ne_nil nonempty
  have hm : c∈cs.filter (fun c => c.packet==⟨d.ifindex,id⟩ &&
      c.owner==⟨d.ifindex,pid,p.internalId⟩ && c.phase==.queued) := by rw [eq]; simp
  obtain ⟨mem,test⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true,beq_iff_eq] at test
  exact ⟨c,mem,test.1.1,test.1.2,test.2⟩

theorem carrier_other (hi : Inventory (c::cs) w) (hx : x∈cs) : x.packet≠c.packet := by
  have ne := (List.nodup_cons.mp hi.distinct).1
  intro he
  exact ne (List.mem_map.mpr ⟨x,hx,he⟩)

theorem head_carrier_unique {id : SkbId} (hi : Inventory (c::cs) w) (hq : QueueOwners (c::cs) w)
    (hd : w.k.wg=some d) (hp : d.peers[pid]?=some p) (cp : c.packet=⟨d.ifindex,id⟩)
    (head : p.rxQueue.all.head?=some id) : c.owner=⟨d.ifindex,pid,p.internalId⟩ ∧ c.phase=.queued := by
  obtain ⟨x,hx,hpacket,owner,phase⟩ := queued_head hq hd hp head
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨owner,phase⟩
  · exact (carrier_other hi hx (hpacket.trans cp.symm)).elim

theorem StableRx.free (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (hq : QueueOwners (c::cs) w) (notqueued : c.phase≠.queued)
    (hr : (freeRxSkb c.packet.slot).run w=.ok ((),v)) : StableRx cs v := by
  obtain ⟨_,pkt,stored,_⟩ := hi.present c (by simp)
  obtain ⟨d,hd,epoch,hpkt⟩ : ∃d,w.k.wg=some d ∧ d.ifindex=c.packet.epoch ∧ d.rxSkbs[c.packet.slot]?=some pkt := by
    cases hd:w.k.wg with
    | none => simp [packetAt,hd] at stored
    | some d =>
      by_cases he:d.ifindex=c.packet.epoch
      · exact ⟨d,rfl,he,by simpa [packetAt,hd,he] using stored⟩
      · simp [packetAt,hd,he] at stored
  have cp : c.packet=⟨d.ifindex,c.packet.slot⟩ := congrArg (fun e => Packet.mk e c.packet.slot) epoch.symm
  rw [Packets.freeRxSkb_run w d c.packet.slot pkt hd hpkt] at hr
  cases hr
  let v := Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.erase c.packet.slot}
  have keeps : ∀x∈cs,packetAt v x.packet=packetAt w x.packet := by
    intro x hx
    obtain ⟨_,q,hq,_⟩ := hi.present x (by simp [hx])
    have ep : d.ifindex=x.packet.epoch := by
      by_cases he:d.ifindex=x.packet.epoch
      · exact he
      · simp [packetAt,hd,he] at hq
    have ne : c.packet.slot≠x.packet.slot := by
      intro he
      apply carrier_other hi hx
      exact (congrArg (fun e => Packet.mk e x.packet.slot) (ep.symm.trans epoch)).trans (congrArg (Packet.mk c.packet.epoch) he.symm)
    simp [v,packetAt,Packets.update,hd,ep,Std.TreeMap.getElem?_erase,ne]
  refine ⟨hs.queued,?_,?_⟩
  · intro out hout
    have eq : out={d with rxSkbs:=d.rxSkbs.erase c.packet.slot} := by simpa [Packets.update,hd] using hout.symm
    subst out
    rw [uncrypted_eq keeps]
    exact hs.ring d hd
  · intro out pid p id hout hp cold head
    have eq : out={d with rxSkbs:=d.rxSkbs.erase c.packet.slot} := by simpa [Packets.update,hd] using hout.symm
    subst out
    have ne : c.packet.slot≠id := by
      intro he
      exact notqueued (head_carrier_unique hi hq hd hp (by simpa [he] using cp) head).2
    obtain ⟨q,hq,state⟩ := hs.cold d pid p id hd hp cold head
    exact ⟨q,by simpa [Std.TreeMap.getElem?_erase,ne] using hq,state⟩


theorem stable_discard (hs : StableRx cs w) (hi : CarrierState (c::cs) loans w)
    (phase : c.phase=.unpublished) (owner : pkt.peer=c.owner.slot)
    (hr : (discard c.packet.slot pkt).run w=.ok ((),v)) : StableRx cs v := by
  obtain ⟨u,a,hkey,u,b,hpay,hfree⟩ := (by simpa only [discard,MaterialOrigin.bind_ok] using hr)
  cases u
  have fr := Prod.mk.inj (keypairPut_credit_frame (some pkt.keypair) false w () a hkey)
  have ia := inventory_selected (inventory_view hi.inventory fr.2)
  have sa := selected_protected (protected_view hi.funded fr.1) (by simp [phase,Phase.charged])
  have qa : QueueOwners (selected c::cs) a := by
    intro d pid p id hd hp
    simpa [List.filter_cons,selected,phase] using (queueOwners_view hi.queues fr.1) d pid p id hd hp
  obtain ⟨p,hp,_⟩ := selected_credit sa rfl
  obtain ⟨d,hd,ep,hpeer,stamp⟩ := resident_fields hp
  have payment : (peerPut (some (selected c).owner.slot)).run a=.ok ((),b) := by simpa [selected,owner] using hpay
  have ib := inventory_paid (inventory_view ia (peerPut_effect _ a b d p hd hpeer payment).2.2)
  have qb := selected_payment_queues qa rfl hd hpeer payment
  have stable := ((hs.view (stable_keypairPut (some pkt.keypair) false w () a hkey)).put hpay)
  exact stable.free ib qb (by simp [paid]) hfree

theorem stable_peerGet (pid : PeerId) : SameView stableView (peerGet pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet,requireNotPending,getPeer,getDev,getK,setPeer,modifyDev,modifyK,
    refcountInc,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [stableView,RxRing.cell,rxView]
  all_goals subst_vars
  all_goals simp_all
  all_goals funext q
  all_goals by_cases he:pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

def publicationDevice (d : Device) (id : SkbId) (pkt : RxPacket) (pid : PeerId) (p : Peer) : Device :=
  {d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=.dead},peers:=d.peers.insert pid {p with napiScheduled:=true}}

theorem publicationMiddle_effect {id : SkbId} {pkt : RxPacket}
    (hd : w.k.wg=some d) (hp : d.peers[pid]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (hr : (publicationMiddle pid id .dead).run w=.ok ((),v)) :
    v.k={w.k with wg:=some (publicationDevice d id pkt pid p)} := by
  have post : ⦃fun z => ⌜z.k=w.k⌝⦄ publicationMiddle pid id .dead
      ⦃⇓? _ z => ⌜z.k={w.k with wg:=some (publicationDevice d id pkt pid p)}⌝⦄ := by
    mvcgen [publicationMiddle,getPeer,getRxSkb,setRxSkb,getDev,getK,setPeer,modifyDev,modifyK,invariant]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [hd,hp,hpacket,publicationDevice]
  exact (hoare_iff_triple _ _ _).mpr post w () v rfl hr

theorem stable_publicationMiddle (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (queues : QueueOwners (c::cs) w) (owner : c.owner.slot=pid)
    (hr : (publicationMiddle pid c.packet.slot .dead).run w=.ok ((),v)) :
    StableRx cs v ∧ ∃pkt,packetAt v c.packet=some pkt ∧ pkt.state=.dead := by
  obtain ⟨_,pkt,stored,_⟩ := hi.present c (by simp)
  obtain ⟨d,p,hd,hp⟩ : ∃d p,w.k.wg=some d ∧ d.peers[pid]?=some p := by
    cases hd:w.k.wg with
    | none => simp [publicationMiddle,getPeer,getDev,getK,hd,invariant] at hr
    | some d =>
      cases hp:d.peers[pid]? with
      | none => simp [publicationMiddle,getPeer,getDev,getK,hd,hp,invariant] at hr
      | some p => exact ⟨d,p,rfl,hp⟩
  have epoch : d.ifindex=c.packet.epoch := by
    by_cases he:d.ifindex=c.packet.epoch
    · exact he
    · simp [packetAt,hd,he] at stored
  have hpacket : d.rxSkbs[c.packet.slot]?=some pkt := by simpa [packetAt,hd,epoch] using stored
  have effect := publicationMiddle_effect hd hp hpacket hr
  let v0 : World := {w with k:={w.k with wg:=some (publicationDevice d c.packet.slot pkt pid p)}}
  have keeps : ∀x∈cs,packetAt v0 x.packet=packetAt w x.packet := by
    intro x hx
    obtain ⟨_,q,hq,_⟩ := hi.present x (by simp [hx])
    have ep : d.ifindex=x.packet.epoch := by
      by_cases he:d.ifindex=x.packet.epoch
      · exact he
      · simp [packetAt,hd,he] at hq
    have ne : c.packet.slot≠x.packet.slot := by
      intro he
      apply carrier_other hi hx
      exact (congrArg (fun e => Packet.mk e x.packet.slot) (ep.symm.trans epoch)).trans (congrArg (Packet.mk c.packet.epoch) he.symm)
    simp [v0,packetAt,publicationDevice,hd,ep,Std.TreeMap.getElem?_insert,ne]
  have stable : StableRx cs v0 := by
    refine ⟨hs.queued,?_,?_⟩
    · intro out hout
      have eq : out=publicationDevice d c.packet.slot pkt pid p := Option.some.inj hout.symm
      subst out
      rw [uncrypted_eq keeps]
      exact hs.ring d hd
    · intro out qid q id hout hq cold head
      have eq : out=publicationDevice d c.packet.slot pkt pid p := Option.some.inj hout.symm
      subst out
      by_cases same : pid=qid
      · subst qid
        have eq : q={p with napiScheduled:=true} := by simpa [publicationDevice] using hq.symm
        simp [eq] at cold
      · have oldq : d.peers[qid]?=some q := by simpa [publicationDevice,Std.TreeMap.getElem?_insert,same] using hq
        have ne : c.packet.slot≠id := by
          intro he
          have own := (head_carrier_unique hi queues hd oldq (by rw [←he]; exact congrArg (fun e=>Packet.mk e c.packet.slot) epoch.symm) head).1
          exact same (owner.symm.trans (congrArg Owner.slot own))
        obtain ⟨stored,hstored,hstate⟩ := hs.cold d qid q id hd oldq cold head
        exact ⟨stored,by simpa [publicationDevice,Std.TreeMap.getElem?_insert,ne] using hstored,hstate⟩
  refine ⟨stable.kernel effect,?_⟩
  exact ⟨{pkt with state:=.dead},by simp [packetAt,effect,publicationDevice,epoch],rfl⟩


theorem compatible_peerDeref (hc : KeyCompatible owner kid w)
    (hr : (IndexOwner.peerDeref (.keypair kid)).run w=.ok (pid,v)) : pid=owner := by
  cases hd:w.k.wg with
  | none => simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,invariant] at hr
  | some d =>
    cases hk:d.keypairs[kid]? with
    | none => simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,invariant] at hr
    | some k =>
      have compatible := hc d k hd hk
      cases hw:k.peer with
      | none => simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,hw,unsupported] at hr
      | some q =>
        simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,getK,hd,hk,hw] at hr
        obtain ⟨rfl,rfl⟩ := hr
        simpa [Affiliation.Compatible,hw] using compatible

theorem peerPut_rxView (pid : Option PeerId) : SameView rxView (peerPut pid) := by
  apply SameView.of_wp
  intro s
  simp only [peerPut,indexRemove_eq]
  mvcgen [indexUnhash,requireNotPending,getPeer,getDev,getK,setPeer,modifyDev,modifyK,
    refcountDecAndTest,retirePeerUnits,branch,branchCmp,invariant,unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [rxView,Option.map_map,Option.bind_map,Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem StableRx.add_dead (hs : StableRx cs w) (phase : c.phase=.queued)
    (stored : packetAt w c.packet=some pkt) (state : pkt.state=.dead) : StableRx (c::cs) w := by
  refine ⟨?_,?_,hs.cold⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact phase
    · exact hs.queued x hx
  · intro d hd
    have contents : uncrypted (c::cs) w=uncrypted cs w := by
      simp only [uncrypted,List.filter_cons,stored,Option.any_some,state]
      rfl
    rw [contents]
    exact hs.ring d hd

/-- The actual pure-IRQ EPIPE publication makes precisely the new queued cell
ready, schedules its own peer, and repays the temporary publication reference. -/
theorem stable_publication (hs : StableRx cs w) (hi : CarrierState (c::cs) loans w)
    (phase : c.phase=.queued)
    (hr : (enqueuePerPeerRx (pure ()) c.packet.slot .dead).run w=.ok ((),v)) : StableRx (c::cs) v := by
  rw [publication_factor] at hr
  obtain ⟨pkt,a,hread,pid,b,hderef,u,q,hget,u,e,hmid,hput⟩ := (by simpa only [MaterialOrigin.bind_ok] using hr)
  have ka := (Packets.getRxSkb_current c.packet.slot w a pkt hread).1
  subst a
  obtain ⟨d,hd,hslot⟩ := (Packets.getRxSkb_current c.packet.slot w w pkt hread).2
  obtain ⟨_,old,hold,owner⟩ := hi.inventory.present c (by simp)
  have epoch : d.ifindex=c.packet.epoch := by
    by_cases he:d.ifindex=c.packet.epoch
    · exact he
    · simp [packetAt,hd,he] at hold
  have stored : packetAt w c.packet=some pkt := by simp [packetAt,hd,epoch,hslot]
  have eq : old=pkt := Option.some.inj (hold.symm.trans stored)
  subst old
  have resolved : pid=pkt.peer := compatible_peerDeref (hi.packet_key stored) hderef
  have kb := indexOwner_peerDeref_sameKernel (.keypair pkt.keypair) w pid b hderef
  obtain ⟨dev,p,hdev,hp,pos,handoff⟩ := peerGet_handoff hget
  have hb : CarrierState (c::cs) loans b := hi.kernel kb
  have iq := inventory_view hb.inventory handoff.rx
  have qq := queueOwners_base hb.queues handoff.base
  have stableq := (hs.kernel kb).view (stable_peerGet pid b () q hget)
  obtain ⟨stable,dead,hdead,state⟩ := stable_publicationMiddle stableq iq qq (owner.symm.trans resolved.symm) hmid
  have keep := peerPut_rxView (some pid) e () v hput
  exact (stable.put hput).add_dead phase ((packetAt_view keep).trans hdead) state


theorem finishAfter_stable (ctx : RxOrigin.Admission) (stable : StableRx cs w)
    (hi : CarrierState (c::cs) loans w) (phase : c.phase=.unpublished)
    (slot : c.packet.slot=ctx.slot) (stored : packetAt w c.packet=some ctx.packet)
    (owner : ctx.packet.peer=c.owner.slot) (state : ctx.packet.state=.uncrypted)
    (physical : RxRing.Inv epoch (PtrRing.init n) h w)
    (he : (enqueuePerDeviceAndPeerRx ctx.slot).run w=.ok (ret,a))
    (ht : (finishAfter ctx ret).run a=.ok ((),v)) :
    if ret=-ENOSPC then StableRx cs v else StableRx (enqueued c::cs) v := by
  have demand : 0<demand (c::cs) loans c.owner := by simp [demand,phase,Phase.charged]; omega
  obtain ⟨p,hp,_⟩ := protected_resident hi.funded demand
  obtain ⟨d,hd,epoch,hpeer,stamp⟩ := resident_fields hp
  have ep : d.ifindex=c.packet.epoch := epoch.trans (hi.inventory.present c (by simp)).1.symm
  have cp : c.packet=⟨d.ifindex,ctx.slot⟩ :=
    (congrArg (fun e => Packet.mk e c.packet.slot) ep.symm).trans (congrArg (Packet.mk d.ifindex) slot)
  have hpacket : d.rxSkbs[ctx.slot]?=some ctx.packet := by simpa [packetAt,hd,ep,slot] using stored
  obtain ⟨ring,href,hcell⟩ := physical
  have ringEq : ring=d.decryptQueue := by simpa [RxRing.cell,hd] using congrArg (Option.map Prod.snd) hcell.symm
  have stableAfter := stable_enqueue (c:=c) stable hd (by simpa [owner] using hpeer) hpacket state cp (ringEq ▸ href) he
  obtain ⟨choices,ha⟩ := enqueue_state hi phase stored owner (by simpa [slot] using he)
  rcases choices with rfl | rfl | rfl
  · have hv : v=CounterWindow.record (CounterWindow.record a .dataEpipe false) .dataEnqueueOk true := by
      simpa [finishAfter,WG.orM,branch,EPIPE,ENOSPC,CounterWindow.record] using ht.symm
    have ready : StableRx (enqueued c::cs) a := by simpa using stableAfter
    simpa [ENOSPC] using ready.kernel (by rw [hv]; rfl)
  · have run : (discard c.packet.slot ctx.packet).run (enospcDecisions a)=.ok ((),v) := by
      simpa [finishAfter,WG.orM,branch,EPIPE,ENOSPC,enospcDecisions,CounterWindow.record,slot] using ht
    have initial : CarrierState (c::cs) loans a := by simpa using ha
    have ready : StableRx cs a := by simpa [ENOSPC] using stableAfter
    simpa using stable_discard (ready.kernel (v:=enospcDecisions a) rfl) (initial.kernel rfl) phase owner run
  · simp only [finishAfter,StateT.run_bind,CounterWindow.branch_run] at ht
    simp only [beq_self_eq_true,CounterWindow.except_ok_bind,↓reduceIte] at ht
    obtain ⟨u,b,hpublish,tail⟩ := bind_ok ht
    cases u
    have initial : CarrierState (enqueued c::cs) loans a := by simpa [ENOSPC,EPIPE] using ha
    have ready : StableRx cs a := by simpa [EPIPE] using stableAfter
    have hb := stable_publication (ready.kernel (v:=CounterWindow.record a .dataEpipe true) rfl)
      (initial.kernel rfl) (by rfl) (by simpa [enqueued,slot] using hpublish)
    have hv : v=CounterWindow.record (CounterWindow.record b .dataEnqueueOk false) .dataEnqueueOkEpipe true := by
      simpa [WG.orM,branch,EPIPE,CounterWindow.record] using tail.symm
    simpa [ENOSPC,EPIPE] using hb.kernel (by rw [hv]; rfl)

theorem admit_ring (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    SameView RxRing.cell (RxOrigin.admitSource msg src ds) := by
  apply SameView.of_wp
  intro s
  have hl := (RxRing.indexLookup_frame [.keypair] (u32le msg 4)).wp (fun t=>t=s)
  have hg := fun k => (RxRing.keypairGet_frame k).wp (fun t=>t=s)
  have hp := fun p => (RxRing.getPeer_frame p).wp (fun t=>t=s)
  have hk := fun k b => (RxRing.keypairPut_frame k b).wp (fun t=>t=s)
  have hput := fun p => (RxRing.peerPut_frame p).wp (fun t=>t=s)
  have hn := fun pkt => (RxRing.newRx_frame pkt).wp (fun t=>t=s)
  have hnull := (RxRing.kernel keypairGetCurrent_sameKernel).wp (fun t=>t=s)
  mvcgen [RxOrigin.admitSource,RxOrigin.admitWith,hl,hg,hp,hk,hput,hn,hnull,branch,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all

/-- The returned ledger is fixed by the actual admission and enqueue outcome.
Both its credit product and its stable ring/head boundary hold; a dead
publication is processable as a drop, not a crypted delivery. -/
def StableConsumption (cs : Ledger) (loans : Reservations) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) (w v : World)
    (r : RunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before=w ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after=v ∧ CarrierState cs loans v ∧ StableRx cs v
  | some ctx => ∃ o,
      let c : Carrier := ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩
      CarrierState (c::cs) loans r.after ∧ o.slot=ctx.packet.peer ∧
      KeyWord ctx.packet.keypair ctx.packet.peer r.after ∧
      RxOrigin.Admitted msg src ds ctx w r.after ∧
      ∃ ret a, (enqueuePerDeviceAndPeerRx ctx.slot).run r.after=.ok (ret,a) ∧
        (finishAfter ctx ret).run a=.ok ((),v) ∧
        (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        (if ret=-ENOSPC then CarrierState cs loans v ∧ StableRx cs v ∧ packetAt v c.packet=none
         else CarrierState (enqueued c::cs) loans v ∧ StableRx (enqueued c::cs) v)

theorem StableConsumption.consumption (h : StableConsumption cs loans msg src ds w v r) :
    Consumption cs loans msg src ds w v r := by
  obtain ⟨before,valid,rest⟩ := h
  refine ⟨before,valid,?_⟩
  cases value:r.value with
  | none => simpa [value] using (show r.after=v ∧ CarrierState cs loans v from ⟨(value ▸ rest).1,(value ▸ rest).2.1⟩)
  | some ctx =>
    simp only [value] at rest ⊢
    obtain ⟨o,hi,owner,key,admitted,ret,a,he,ht,choice,result⟩ := rest
    refine ⟨o,hi,owner,key,admitted,ret,a,he,ht,choice,?_⟩
    by_cases hret : ret = -ENOSPC <;> simp_all [hret]

/-- Original whole-call normal conservation. The physical premise is the
existing ring journal, and no endpoint World is assigned to a Stop. -/
theorem consume_stable (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (hs : StableRx cs w) (physical : RxRing.Inv epoch (PtrRing.init n) h w)
    (hr : (consumeData msg src ds).run w=.ok ((),v)) :
    ∃r,StableConsumption cs loans msg src ds w v r := by
  obtain ⟨r,before,valid,result⟩ := consume_normal hi hf hr
  refine ⟨r,before,valid,?_⟩
  have hfront : (RxOrigin.admitSource msg src ds).run w=.ok (r.value,r.after) := by simpa [RunWitness.Valid,before] using valid
  cases value:r.value with
  | none =>
    simp only [value] at result ⊢
    have stable : StableRx cs r.after := admitted_none_stable hs (by simpa [value] using hfront)
    exact ⟨result.1,result.2,result.1 ▸ stable⟩
  | some ctx =>
    simp only [value] at result ⊢
    obtain ⟨o,ha,owner,key,admitted,ret,a,he,ht,choices,endpoint⟩ := result
    have front : (RxOrigin.admitSource msg src ds).run w=.ok (some ctx,r.after) := by simpa [value] using hfront
    have stable := admitted_stable_front hs hi.inventory hf front
    have physicalAfter : RxRing.Inv epoch (PtrRing.init n) h r.after := by
      obtain ⟨ring,href,hcell⟩ := physical
      exact ⟨ring,href,(admit_ring msg src ds w _ r.after front).trans hcell⟩
    obtain ⟨_,pkt,hpkt,_⟩ := ha.inventory.present ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ (by simp)
    have eq : pkt=ctx.packet := admitted_packet front hpkt
    subst pkt
    have state : ctx.packet.state=.uncrypted := by
      obtain ⟨entry,b,c,d,peer,e,f,hl,hk,hno,hpeer,hdead,packet,alloc⟩ := admitted
      rw [packet]
    have finalStable := finishAfter_stable ctx stable ha rfl rfl hpkt owner.symm state physicalAfter he ht
    refine ⟨o,ha,owner,key,admitted,ret,a,he,ht,choices,?_⟩
    by_cases hret : ret = -ENOSPC <;> simp_all [hret]

/-- The existing ring observer on this same original normal execution supplies
its actual appended physical journal and endpoint refinement. This is a local
supplied-history result, not initialized pipeline correspondence. -/
theorem consume_ring_normal (physical : RxRing.Inv epoch (PtrRing.init n) h w)
    (hr : (consumeData msg src ds).run w=.ok ((),v)) :
    let out := runPrefix (RxRing.consume msg src ds) w h
    out.1=.ok ((),v) ∧ (∃suffix,out.2=h++suffix) ∧
      RxRing.Safe (PtrRing.init n) out.2 ∧ RxRing.Inv epoch (PtrRing.init n) out.2 v := by
  have erasure := (RxRing.consume_erases msg src ds w h).trans hr
  obtain ⟨suffix,append,safe,post⟩ := RxRing.consume_preserves msg src ds w h physical
  rw [erasure] at post
  exact ⟨erasure,⟨suffix,append⟩,safe,post⟩

end Leanux.Proofs.WG.Queues.RxCredits
