import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Queues.RxPollStable

/-! Exact picked-ring and ready-publication boundaries. The picked packet stays
in the funded carrier ledger while it is temporarily absent from the ring. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DecryptStable
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

theorem ring_consume_items {id : SkbId} {next : PtrRing SkbId} (hr : RxRing.Refines (PtrRing.init n) h r)
    (hc : r.consume=(some id,next)) : r.items=id::next.items := by
  have old := hr.initialized.2.1
  have after := (hr.step .poll).initialized.2.1
  simp only [Ring.Journal.step,hc] at after
  simp only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,List.append_nil] at after old
  rw [old,List.append_assoc] at after
  exact List.append_cancel_left after

theorem picked_stable {id : SkbId} (hs : StableRx (c::cs) w) (hi : Inventory (c::cs) w)
    (hd : w.dev=some d) (cp : c.packet=⟨d.ifindex,id⟩)
    (physical : RxRing.Refines (PtrRing.init n) h d.decryptQueue)
    (consumed : d.decryptQueue.consume=(some id,ring)) :
    StableRx cs {w with dev:=some {d with decryptQueue:=ring}} ∧
      ∃pkt,packetAt w c.packet=some pkt ∧ pkt.state=.uncrypted := by
  have contents := ring_consume_items physical consumed
  obtain ⟨_,pkt,stored,_⟩ := hi.present c (by simp)
  have mem : c.packet∈uncrypted (c::cs) w := by
    apply (hs.ring d hd).mem_iff.mp
    simp [contents,cp]
  have state : pkt.state=.uncrypted := by
    apply Classical.byContradiction
    intro hn
    have other : c.packet∈uncrypted cs w := by
      have test : (packetAt w c.packet).any (fun p => p.state == .uncrypted)=false := by
        rw [stored]
        cases he : pkt.state <;> simp_all <;> rfl
      simpa only [uncrypted,List.filter_cons,test,Bool.false_eq_true,ite_false] using mem
    obtain ⟨x,hx,he⟩ := List.mem_map.mp other
    exact carrier_other hi (List.mem_filter.mp hx).1 he
  refine ⟨⟨?_,?_,?_⟩,pkt,stored,state⟩
  · intro x hx
    exact hs.queued x (by simp [hx])
  · intro out hout
    have eq : out={d with decryptQueue:=ring} := Option.some.inj hout.symm
    subst out
    have perm := hs.ring d hd
    simp only [contents,List.map_cons,←cp,uncrypted,List.filter_cons,stored,
      Option.any_some,state,List.map_cons] at perm
    have tail := List.Perm.cons_inv perm
    simpa [uncrypted,packetAt,hd] using tail
  · intro out pid p slot hout hp cold head
    have eq : out={d with decryptQueue:=ring} := Option.some.inj hout.symm
    subst out
    exact hs.cold d pid p slot hd hp cold head

def readyDevice (d : Device) (id : SkbId) (pkt : RxPacket) (pid : PeerId) (p : Peer) (state : PacketState) : Device :=
  {d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=state},peers:=d.peers.insert pid {p with napiScheduled:=true}}

theorem ready_effect {id : SkbId} {pkt : RxPacket} (state : PacketState)
    (hd : w.dev=some d) (hp : d.peers[pid]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (ambient ambient' : Ambient)
    (hr : ((publicationMiddle pid id state).run w).run ambient=.ok (((),v),ambient')) :
    wgStoreView v={wgStoreView w with dev:=some (readyDevice d id pkt pid p state)} := by
  unfold publicationMiddle at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨q,a,aa,hg,hr⟩ := hr
  obtain ⟨ha,haa,d',hd',hq⟩ := getPeer_normal pid w a q ambient aa hg
  have eqd : d'=d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  have eqp : q=p := Option.some.inj (hq.symm.trans hp)
  subst q
  subst a
  subst aa
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,ite_true] at hr
    cases hr
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,ite_false] at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨x,b,midway,hs,ht⟩ := hr
    have exactSet := Packets.setRxSkb_run w ambient d id pkt (fun q => {q with state:=state}) hd hpacket
    rw [hs] at exactSet
    cases exactSet
    cases ht
    simp [wgStoreView,readyDevice,Packets.update,hd]


theorem publicationMiddle_stable (state : PacketState) (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (queues : QueueOwners (c::cs) w) (owner : c.owner.slot=pid)
    (ambient ambient' : Ambient)
    (hr : ((publicationMiddle pid c.packet.slot state).run w).run ambient=.ok (((),v),ambient')) :
    StableRx cs v ∧ ∃pkt,packetAt v c.packet=some pkt ∧ pkt.state=state := by
  obtain ⟨_,pkt,stored,_⟩ := hi.present c (by simp)
  have source := hr
  unfold publicationMiddle at source
  rw [MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨p,a,aa,hg,_⟩ := source
  obtain ⟨_,_,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hg
  have epoch : d.ifindex=c.packet.epoch := by
    by_cases he:d.ifindex=c.packet.epoch
    · exact he
    · simp [packetAt,hd,he] at stored
  have hpacket : d.rxSkbs[c.packet.slot]?=some pkt := by simpa [packetAt,hd,epoch] using stored
  have effect := ready_effect state hd hp hpacket ambient ambient' hr
  let v0 : WGWorld := {w with dev:=some (readyDevice d c.packet.slot pkt pid p state)}
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
    simp [v0,packetAt,readyDevice,hd,ep,Std.TreeMap.getElem?_insert,ne]
  have stable : StableRx cs v0 := by
    refine ⟨hs.queued,?_,?_⟩
    · intro out hout
      have eq : out=readyDevice d c.packet.slot pkt pid p state := Option.some.inj hout.symm
      subst out
      rw [uncrypted_eq keeps]
      exact hs.ring d hd
    · intro out qid q id hout hq cold head
      have eq : out=readyDevice d c.packet.slot pkt pid p state := Option.some.inj hout.symm
      subst out
      by_cases same : pid=qid
      · subst qid
        have eq : q={p with napiScheduled:=true} := by simpa [readyDevice] using hq.symm
        simp [eq] at cold
      · have oldq : d.peers[qid]?=some q := by simpa [readyDevice,Std.TreeMap.getElem?_insert,same] using hq
        have ne : c.packet.slot≠id := by
          intro he
          have own := (head_carrier_unique hi queues hd oldq (by rw [←he]; exact congrArg (fun e=>Packet.mk e c.packet.slot) epoch.symm) head).1
          exact same (owner.symm.trans (congrArg Owner.slot own))
        obtain ⟨stored,hstored,hstate⟩ := hs.cold d qid q id hd oldq cold head
        exact ⟨stored,by simpa [readyDevice,Std.TreeMap.getElem?_insert,ne] using hstored,hstate⟩
  refine ⟨stable.kernel effect,?_⟩
  have dev := congrArg WGStoreView.dev effect
  change v.dev=some (readyDevice d c.packet.slot pkt pid p state) at dev
  exact ⟨{pkt with state:=state},by simp [packetAt,dev,readyDevice,epoch],rfl⟩


theorem add_ready (hs : StableRx cs w) (phase : c.phase=.queued)
    (stored : packetAt w c.packet=some pkt) (ready : pkt.state≠.uncrypted) : StableRx (c::cs) w := by
  refine ⟨?_,?_,hs.cold⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact phase
    · exact hs.queued x hx
  · intro d hd
    have contents : uncrypted (c::cs) w=uncrypted cs w := by
      have test : (packetAt w c.packet).any (fun p => p.state == .uncrypted)=false := by
        rw [stored]
        cases he : pkt.state <;> simp_all <;> rfl
      simp only [uncrypted,List.filter_cons,test,Bool.false_eq_true,ite_false]
    rw [contents]
    exact hs.ring d hd


/-- A picked packet is ready again after the actual publication prefix. The
extra reference is deliberately not repaid at this boundary. -/
theorem publish_stable (hs : StableRx cs w) (hi : CarrierState (c::cs) loans w)
    (phase : c.phase=.queued) (state : PacketState) (ready : state≠.uncrypted)
    (ambient ambient' : Ambient)
    (hr : ((RxWorkers.publishSource c.packet.slot state).run w).run ambient=.ok ((pid,v),ambient')) :
    StableRx (c::cs) v := by
  rw [DecryptCarrier.publish_factor] at hr
  obtain ⟨pkt,a,aa,hread,ownerId,b,ab,hderef,u,q,aq,hget,u,e,ae,hmid,hpure⟩ :=
    (by simpa only [MaterialOrigin.bind_ok_ambient] using hr)
  cases hpure
  have ka := (Packets.getRxSkb_current c.packet.slot w a pkt ambient aa hread).1
  subst a
  obtain ⟨_,d,hd,hslot⟩ := (Packets.getRxSkb_current c.packet.slot w w pkt ambient aa hread).2
  obtain ⟨_,old,hold,owner⟩ := hi.inventory.present c (by simp)
  have epoch : d.ifindex=c.packet.epoch := by
    by_cases he:d.ifindex=c.packet.epoch
    · exact he
    · simp [packetAt,hd,he] at hold
  have stored : packetAt w c.packet=some pkt := by simp [packetAt,hd,epoch,hslot]
  have eq : old=pkt := Option.some.inj (hold.symm.trans stored)
  subst old
  have resolved : pid=pkt.peer := compatible_peerDeref (hi.packet_key stored) aa ab hderef
  have kb : b=w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun g=>g=w)) w aa pid b ab rfl hderef
  obtain ⟨dev,p,hdev,hp,pos,handoff⟩ := peerGet_handoff ab aq hget
  have hb : CarrierState (c::cs) loans b := kb ▸ hi
  have iq := inventory_view hb.inventory handoff.rx
  have qq := queueOwners_base hb.queues handoff.base
  have stableq := (show StableRx cs b from kb ▸ hs).view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_peerGet pid) b ab () q aq hget)
  obtain ⟨stable,out,hout,hstate⟩ := publicationMiddle_stable state stableq iq qq
    (owner.symm.trans resolved.symm) aq ambient' hmid
  exact add_ready stable phase hout (hstate ▸ ready)

/-- A payload rewrite leaves the picked packet's phase unchanged and does not
modify the other ledger cells or the cold queue-head obligation. -/
theorem payload_stable (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (hd : w.dev=some d) (hp : d.rxSkbs[c.packet.slot]?=some pkt)
    (state : out.state=pkt.state) :
    StableRx cs (Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.insert c.packet.slot out}) := by
  let v := Packets.update w fun d => {d with rxSkbs:=d.rxSkbs.insert c.packet.slot out}
  obtain ⟨_,old,hold,_⟩ := hi.present c (by simp)
  have epoch : d.ifindex=c.packet.epoch := by
    by_cases he:d.ifindex=c.packet.epoch
    · exact he
    · simp [packetAt,hd,he] at hold
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
    simp [v,packetAt,Packets.update,hd,ep,Std.TreeMap.getElem?_insert,ne]
  refine ⟨hs.queued,?_,?_⟩
  · intro dev hdev
    have eq : dev={d with rxSkbs:=d.rxSkbs.insert c.packet.slot out} := by simpa [Packets.update,hd] using hdev.symm
    subst dev
    rw [uncrypted_eq keeps]
    exact hs.ring d hd
  · intro dev pid p id hdev hpeer cold head
    have eq : dev={d with rxSkbs:=d.rxSkbs.insert c.packet.slot out} := by simpa [Packets.update,hd] using hdev.symm
    subst dev
    obtain ⟨q,hq,hstate⟩ := hs.cold d pid p id hd hpeer cold head
    by_cases same : c.packet.slot=id
    · have eq : q=pkt := Option.some.inj (hq.symm.trans (same ▸ hp))
      subst q
      exact ⟨out,by simp [same],state.trans hstate⟩
    · exact ⟨q,by simpa [Std.TreeMap.getElem?_insert,same] using hq,hstate⟩


theorem picked_exists {id : SkbId} (hs : StableRx cs w) (hi : Inventory cs w)
    (hd : w.dev=some d) (physical : RxRing.Refines (PtrRing.init n) h d.decryptQueue)
    (consumed : d.decryptQueue.consume=(some id,ring)) :
    ∃c rest, cs.Perm (c::rest) ∧ c.packet=⟨d.ifindex,id⟩ ∧
      StableRx rest {w with dev:=some {d with decryptQueue:=ring}} := by
  classical
  have contents := ring_consume_items physical consumed
  have mem : Packet.mk d.ifindex id∈uncrypted cs w := by
    apply (hs.ring d hd).mem_iff.mp
    simp [contents]
  obtain ⟨c,hc,cp⟩ := List.mem_map.mp mem
  have member := (List.mem_filter.mp hc).1
  have perm := List.perm_cons_erase member
  exact ⟨c,cs.erase c,perm,cp,
    (picked_stable (hs.perm perm) (inventory_perm perm hi) hd cp physical consumed).1⟩

theorem readDecrypt_stable (id : SkbId) (hs : StableRx cs w) (a b : Ambient)
    (hr : ((RxOrigin.readDecrypt id).run w).run a=.ok (((pkt,result),v),b)) :
    StableRx cs v ∧ ∀ out, result=some out → out.state=pkt.state := by
  unfold RxOrigin.readDecrypt at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨old,read,ar,hread,decrypted,done,ad,hdecrypt,hpure⟩ := hr
  cases hpure
  have readEq := (Packets.getRxSkb_current id w read pkt a ar hread).1
  subst read
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (DecryptCarrier.decryptPacket_view pkt) w ar result v b hdecrypt
  refine ⟨hs.view (congrArg Prod.snd frame),?_⟩
  intro out hout
  have record := RxOrigin.decryptPacket_record pkt out w v ar b (hout ▸ hdecrypt)
  simpa only using congrArg RxPacket.state record

/-- The actual native worker preparation restores the full stable RX boundary
on normal return. The physical ring hypothesis selects the same carrier; it
is not a liveness or successful-decryption premise. -/
theorem prepare_stable (hi : CarrierState cs loans w) (hs : StableRx cs w)
    (physical : NativeRxInv epoch (PtrRing.init n) h w) (a b : Ambient)
    (hr : ((RxWorkers.prepareSource).run w).run a=.ok ((result,v),b)) :
    StableRx cs v := by
  rw [DecryptCarrier.prepare_factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨d,read,ar,hget,tail⟩ := hr
  obtain ⟨readEq,ambientEq,hd⟩ := DecryptCarrier.getDev_current a ar hget
  subst read; subst ar
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none =>
      simp only [hc,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨value,after,aa,hbranch,hpure⟩ := tail
      change Except.ok ((false,w),CounterWindow.record a .decWorkerConsumed false)=Except.ok ((value,after),aa) at hbranch
      cases hbranch
      cases hpure
      exact hs
    | some id =>
      obtain ⟨oldRing,href,hcell⟩ := physical
      have ringEq : oldRing=d.decryptQueue := by
        simpa [RxRing.nativeCell,hd] using congrArg (Option.map Prod.snd) hcell.symm
      obtain ⟨c,rest,perm,cp,picked⟩ := picked_exists hs hi.inventory hd (ringEq ▸ href) hc
      have hiPicked := hi.perm perm
      have phase := hs.queued c (perm.mem_iff.mpr (by simp))
      simp only [hc,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨value,after,aa,hbranch,u,ringWorld,ab,hring,pair,readWorld,ac,hread,decision,decWorld,ad,hdecision,tail⟩ := tail
      change Except.ok ((true,w),CounterWindow.record a .decWorkerConsumed true)=Except.ok ((value,after),aa) at hbranch
      cases hbranch
      cases hring
      rcases pair with ⟨pkt,decrypted⟩
      have hiRing := DecryptCarrier.ring_state hiPicked ring
      obtain ⟨hiRead,⟨dev,hdev,hpkt⟩,fields⟩ := DecryptCarrier.readDecrypt_state id hiRing _ ac hread
      have stableRing : StableRx rest ({w with dev:=w.dev.map fun d => {d with decryptQueue:=ring}}) := by
        simpa [hd] using picked
      obtain ⟨stableRead,states⟩ := readDecrypt_stable id stableRing _ ac hread
      have slot : c.packet.slot=id := congrArg Packet.slot cp
      change Except.ok ((decrypted.isSome,readWorld),CounterWindow.record ac .decWorkerDecrypted decrypted.isSome)=
        Except.ok ((decision,decWorld),ad) at hdecision
      cases hdecision
      cases decrypted with
      | none =>
        simp only [Option.isSome_none,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨pid,final,af,hpublish,hpure⟩ := tail
        cases hpure
        have actual : ((RxWorkers.publishSource c.packet.slot .dead).run readWorld).run (CounterWindow.record ac .decWorkerDecrypted false)=.ok ((pid,v),b) := by
          simpa only [slot] using hpublish
        exact StableRx.perm (publish_stable stableRead hiRead phase .dead (by decide) _ b actual) perm.symm
      | some out =>
        simp only [Option.isSome_some,ite_true,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨u,updated,au,hwrite,pid,final,af,hpublish,hpure⟩ := tail
        cases u
        cases hpure
        have hiWrite := DecryptCarrier.set_payload_state hiRead hdev hpkt (fields out rfl).1 (fields out rfl).2 _ au hwrite
        have stableWrite : StableRx rest updated := by
          rw [Packets.setRxSkb_run readWorld _ dev id pkt (fun _ => out) hdev hpkt] at hwrite
          cases hwrite
          simpa only [slot] using payload_stable stableRead hiRead.inventory hdev (slot ▸ hpkt) (states out rfl)
        have actual : ((RxWorkers.publishSource c.packet.slot .crypted).run updated).run au=.ok ((pid,v),b) := by
          simpa only [slot] using hpublish
        exact StableRx.perm (publish_stable stableWrite hiWrite phase .crypted (by decide) au b actual) perm.symm

end Leanux.Proofs.WG.Queues.RxCredits.DecryptStable
