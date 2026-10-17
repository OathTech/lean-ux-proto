import Leanux.Proofs.WG.Queues.RxStackProtection
import Leanux.Proofs.WG.Queues.RxPollReceiptLink

/-! Source-connected carrier phases for the normal receive poll. A selected
cell remains charged until its actual peer payment and remains in inventory
until actual free. No endpoint World is assigned to a stopped call. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

structure CarrierState (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop where
  inventory : Inventory cs w
  queues : QueueOwners cs w
  funded : Protected cs loans w
  keys : KeysCompatible w

theorem inventory_perm (hp : xs.Perm ys) (hi : Inventory xs w) : Inventory ys w := by
  refine ⟨(hp.map Carrier.packet).nodup_iff.mp hi.distinct,?_,?_⟩
  · intro c hc; exact hi.present c (hp.mem_iff.mpr hc)
  · intro d id pkt hd hs
    obtain ⟨c,hc,he⟩ := hi.complete d id pkt hd hs
    exact ⟨c,hp.mem_iff.mp hc,he⟩

theorem queues_perm (hp : xs.Perm ys) (hi : QueueOwners xs w) : QueueOwners ys w := by
  intro d pid p id hd hs
  rw [hi d pid p id hd hs]
  exact (hp.filter _).length_eq

theorem protected_perm (hp : xs.Perm ys) (hi : Protected xs loans w) : Protected ys loans w := by
  intro o
  have he : charges xs o = charges ys o := (hp.filter _).length_eq
  simpa only [demand,←he] using hi o

theorem CarrierState.perm (hi : CarrierState xs loans w) (hp : xs.Perm ys) : CarrierState ys loans w :=
  ⟨inventory_perm hp hi.inventory,queues_perm hp hi.queues,protected_perm hp hi.funded,hi.keys⟩

theorem CarrierState.kernel (hi : CarrierState cs loans w)
    (hk : wgStoreView v = wgStoreView w) : CarrierState cs loans v := by
  have hd : v.dev = w.dev := congrArg WGStoreView.dev hk
  have key : keyView v = keyView w := by unfold keyView keyWords currentCells; rw [hd]
  have rx : rxView v = rxView w := by unfold rxView; rw [hd]
  exact ⟨inventory_view hi.inventory rx,
    queueOwners_view hi.queues (by unfold peerView; rw [hd]),
    protected_view hi.funded (by unfold peerView; rw [hd]),
    (keyEffect_of_view (allowed := NoPromotion) key).rxCompatible rx hi.keys.1,
    (keyEffect_of_view (allowed := NoPromotion) key).currentsCompatible hi.keys.2
      (fun _ _ h => h.elim)⟩

theorem CarrierState.transfer (hi : CarrierState cs loans w) (ht : Transfer w v)
    (hk : KeysCompatible v) : CarrierState cs loans v := by
  obtain ⟨delta,hd⟩ := ht
  obtain ⟨hin,hqn,hpn,_⟩ := hd.protect hi.inventory hi.queues hi.funded
  exact ⟨hin,hqn,hpn,hk⟩

theorem CarrierState.packet_key {c : Carrier} (hi : CarrierState cs loans w)
    (hp : packetAt w c.packet = some pkt) : KeyCompatible pkt.peer pkt.keypair w := by
  cases hd : w.dev with
  | none => simp [packetAt,hd] at hp
  | some d =>
    by_cases he : d.ifindex=c.packet.epoch
    · have hs : d.rxSkbs[c.packet.slot]?=some pkt := by simpa [packetAt,hd,he] using hp
      exact hi.keys.1 d c.packet.slot pkt hd hs
    · simp [packetAt,hd,he] at hp

theorem freeRx_rxCompatible (id : SkbId) (hi : RxCompatible w)
    (ambient ambient' : Ambient)
    (hr : ((freeRxSkb id).run w).run ambient = .ok (((),v),ambient')) : RxCompatible v := by
  cases hd : w.dev with
  | none =>
    simp [freeRxSkb,liftSkb_run,hd] at hr
  | some d =>
    cases hs : d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,hd,hs,
        invariant,AmbientM.invariant,StateT.run_bind] at hr
      cases hr
    | some pkt =>
      rw [Packets.freeRxSkb_run w ambient d id pkt hd hs] at hr
      cases hr
      intro out sid p hout hp
      have eq : out={d with rxSkbs:=d.rxSkbs.erase id} := by
        simpa [Packets.update,hd] using hout.symm
      subst out
      have ne : id≠sid := by intro e; simp [e] at hp
      have prior : d.rxSkbs[sid]?=some p := by
        simpa [Std.TreeMap.getElem?_erase,ne] using hp
      have hkey := hi d sid p hd prior
      intro target key htarget hkeyslot
      have he : target={d with rxSkbs:=d.rxSkbs.erase id} := by
        simpa [Packets.update,hd] using htarget.symm
      subst target
      exact hkey d key hd hkeyslot

theorem freeRx_keys (id : SkbId) (hi : KeysCompatible w)
    (ambient ambient' : Ambient)
    (hr : ((freeRxSkb id).run w).run ambient = .ok (((),v),ambient')) : KeysCompatible v := by
  have frame : Preserves (fun g => keyView g = keyView w) (freeRxSkb id) := by
    unfold freeRxSkb
    apply hoare_liftSkb
    intro g d store hg hd
    unfold keyView keyWords currentCells at hg ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hg
  have key := (hoare_iff_run_ambient _ _ _).mp frame w ambient () v ambient' rfl hr
  exact ⟨freeRx_rxCompatible id hi.1 ambient ambient' hr,
    (keyEffect_of_view (allowed := NoPromotion) key).currentsCompatible hi.2
      (fun _ _ h => h.elim)⟩

theorem keyPut_state (kp : Option KeypairId) (now : Bool) (hi : CarrierState cs loans w)
    (ambient ambient' : Ambient)
    (hr : ((keypairPut kp now).run w).run ambient = .ok (((),v),ambient')) : CarrierState cs loans v := by
  have hf := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame kp now) w ambient () v ambient' hr)
  have hk := (KeyEffects.iff_run_ambient _ _).mp
    (keypairPut_keyEffect (allowed := NoPromotion) kp now) w ambient () v ambient' hr
  exact ⟨inventory_view hi.inventory hf.2,queueOwners_view hi.queues hf.1,
    protected_view hi.funded hf.1,hk.rxCompatible hf.2 hi.keys.1,
    hk.currentsCompatible hi.keys.2 (by intro p k h; exact h.elim)⟩

/-- Exact selected-to-paid-to-freed source cut. The supplied normal key-put
endpoint is extracted from the enclosing actual run; no peer survival is assumed. -/
theorem selected_cleanup (hi : CarrierState (c::cs) loans w) (hc : c.phase=.selected)
    (owner : pkt.peer=c.owner.slot) (ambient ambient' : Ambient)
    (hr : ((cleanup c.packet.slot pkt flag).run w).run ambient=.ok (((),v),ambient')) :
    CarrierState cs loans v ∧ packetAt v c.packet=none := by
  unfold cleanup at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,aa,hkey,rest⟩ := hr; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,b,ab,hpeer,rest⟩ := rest; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ret,z,az,hbranch,hfree⟩ := rest
  have ha := keyPut_state _ _ hi ambient aa hkey
  obtain ⟨p,hp,_⟩ := selected_credit ha.funded hc
  obtain ⟨d,hd,_,hpid,_⟩ := resident_fields hp
  have payment : ((peerPut (some c.owner.slot)).run a).run aa=.ok (((),b),ab) := by
    simpa only [owner] using hpeer
  obtain ⟨hprot,hrx,_⟩ := selected_payment_normal ha.funded hc aa ab payment
  have hk := (KeyEffects.iff_run_ambient _ _).mp
    (peerPut_keyEffect (allowed := NoPromotion) (some pkt.peer)) a aa () b ab hpeer
  have kb : KeysCompatible b := ⟨hk.rxCompatible hrx ha.keys.1,
    hk.currentsCompatible ha.keys.2 (by intro p k h; exact h.elim)⟩
  have ib := inventory_paid (inventory_view ha.inventory hrx)
  have qb := selected_payment_queues ha.queues hc hd hpid aa ab payment
  have hz := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (fun g => g = b))
    b ab ret z az rfl hbranch
  subst z
  obtain ⟨out,hout,iv,pv,gone⟩ := paid_free az ib hprot
  have same : out=v := by rw [hfree] at hout; cases hout; rfl
  subst out
  exact ⟨⟨iv,paid_free_queues qb az ambient' hfree,pv,
    freeRx_keys _ kb az ambient' hfree⟩,gone⟩

/-- The actual consume callback preserves the same selected carrier list.
Only the entry packet's resident key word is used for promotion compatibility. -/
theorem consume_state {c : Carrier} (hi : CarrierState cs loans w) (hp : packetAt w c.packet=some pkt)
    (guard : pkt.peer=pid) (ambient ambient' : Ambient)
    (hr : ((consumeDataDone pid pkt ep).run w).run ambient=.ok ((out,v),ambient')) : CarrierState cs loans v := by
  have hkey : KeyCompatible pid pkt.keypair w := guard ▸ hi.packet_key hp
  exact hi.transfer (consumeDataDone_handoff pid pkt ep hkey ambient ambient' hr)
    (consumeDataDone_keys pid pkt ep hi.keys hkey ambient ambient' hr)

theorem stack_state (packets : List (List UInt8)) {w v : World}
    (hi : CarrierState cs loans w.wg)
    (hr : (packets.forM Leanux.Env.deliverInner).run w=.ok ((),v)) : CarrierState cs loans v.wg := by
  obtain ⟨delta,hd,iv,qv,pv,_,kv⟩ := stackForM_protection packets hi.inventory hi.queues hi.funded hi.keys hr
  exact ⟨iv,qv,pv,kv⟩

/-- Allocation identities, not occurrence numbers, determine the remaining
original ledger. No selection is removed from the live invariant before free. -/
def remaining (cs : Ledger) (removed : List Packet) : Ledger :=
  cs.filter fun c => !removed.contains c.packet

theorem remaining_append (cs : Ledger) (a b : List Packet) :
    remaining cs (a++b)=remaining (remaining cs a) b := by
  simp [remaining,List.filter_filter,Bool.and_comm]

/-- A fresh queue-only setter changes no credit, packet or compatible key.
The logical queue includes its cached head. -/
theorem queue_update_state (hi : CarrierState cs loans w)
    (hd : w.dev=some d) (hp : d.peers[pid]?=some p) (q : PrevQueue SkbId)
    (hq : q.all=p.rxQueue.all) :
    CarrierState cs loans {w with dev:=some {d with peers:=d.peers.insert pid {p with rxQueue:=q}}} := by
  let v := {w with dev:=some {d with peers:=d.peers.insert pid {p with rxQueue:=q}}}
  have rx : rxView v=rxView w := by simp [v,rxView,hd]
  have key : keyView v=keyView w := keyView_set_peer hd hp rfl
  refine ⟨inventory_view hi.inventory rx,?_,?_,(keyEffect_of_view (allowed:=NoPromotion) key).rxCompatible rx hi.keys.1,
    (keyEffect_of_view (allowed := NoPromotion) key).currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩
  · intro out qid op id hout ho
    have he : out={d with peers:=d.peers.insert pid {p with rxQueue:=q}} := by simpa [v] using hout.symm
    subst out
    by_cases same : pid=qid
    · subst qid
      have he : op={p with rxQueue:=q} := by simpa using ho.symm
      subst op
      simpa [hq] using hi.queues d pid p id hd hp
    · have old : d.peers[qid]?=some op := by simpa [Std.TreeMap.getElem?_insert,same] using ho
      exact hi.queues d qid op id hd old
  · intro o
    have bal : balance v o=balance w o := by
      simp only [balance_factor,peerView,viewBalance,v,hd,Option.map_some,Option.bind_some]
      by_cases same : pid=o.slot <;> simp [Std.TreeMap.getElem?_insert,same]
      simp [←same,hp]
    change demand cs loans o ≤ balance v o
    rw [bal]
    exact hi.funded o

def Peeked (pid : PeerId) (first : Option SkbId) (w : WGWorld) : Prop :=
  ∃ d p,w.dev=some d ∧ d.peers[pid]?=some p ∧ p.rxQueue.peeked=first

theorem peek_state (pid : PeerId) (hi : CarrierState cs loans w)
    (ambient ambient' : Ambient)
    (hr : ((peekRxQueue pid).run w).run ambient=.ok ((first,v),ambient')) :
    CarrierState cs loans v ∧ Peeked pid first v := by
  unfold peekRxQueue at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,rest⟩ := hr
  obtain ⟨ha,haa,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hget
  subst a; subst aa
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨out,b,ab,hpeek,rest⟩ := rest
  rcases out with ⟨head,q⟩
  obtain ⟨_,hall,hcache,hb⟩ := prev_peek_normal p.rxQueue w b ambient ab head q hpeek
  subst b
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨p2,a,aa,hget2,rest⟩ := rest
  obtain ⟨ha,haa,d2,hd2,hp2⟩ := getPeer_normal pid w a p2 ab aa hget2
  subst a; subst aa
  have deq : d2=d := by rw [hd] at hd2; cases hd2; rfl
  subst d2
  have peq : p2=p := by rw [hp] at hp2; cases hp2; rfl
  subst p2
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,a,aa,hset,rest⟩ := rest; cases u
  simp only [StateT.run_pure] at rest
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
  have target : v={w with dev:=some {d with peers:=d.peers.insert pid {p with rxQueue:=q}}} := by
    cases hset
    simp [hd]
  subst v
  exact ⟨queue_update_state hi hd hp q hall,
    ⟨{d with peers:=d.peers.insert pid {p with rxQueue:=q}},{p with rxQueue:=q},rfl,by simp,hcache⟩⟩

/-- The original queue occurrence identifies an actual charged carrier; a
packet label cannot be assigned to an unrelated peer merely by a journal event. -/
theorem queued_carrier {id : SkbId} (hi : CarrierState cs loans w) (hd : w.dev=some d)
    (hp : d.peers[pid]?=some p) (peek : p.rxQueue.peeked=some id) :
    (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ : Carrier) ∈ cs := by
  have pos : 0<p.rxQueue.all.count id := by simp [PrevQueue.all,peek]
  rw [hi.queues d pid p id hd hp] at pos
  have hex : ∃ c∈cs,(c.packet=⟨d.ifindex,id⟩ ∧ c.owner=⟨d.ifindex,pid,p.internalId⟩) ∧ c.phase=.queued := by
    let xs := cs.filter fun c => c.packet==⟨d.ifindex,id⟩ && c.owner==⟨d.ifindex,pid,p.internalId⟩ && c.phase==.queued
    have hn : xs≠[] := List.length_pos_iff.mp pos
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil xs hn
    simpa only [xs,List.mem_filter,Bool.and_eq_true,beq_iff_eq] using (show ∃x,x∈xs from ⟨x,hx⟩)
  obtain ⟨c,hc,hfields⟩ := hex
  have fields : c.packet=⟨d.ifindex,id⟩ ∧ c.owner=⟨d.ifindex,pid,p.internalId⟩ ∧ c.phase=.queued := by
    exact ⟨hfields.1.1,hfields.1.2,hfields.2⟩
  have eq : c=⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ := by
    cases c; simp_all
  simpa [eq] using hc

theorem remaining_one_perm (hi : (cs.map Carrier.packet).Nodup) (hp : cs.Perm (c::rest)) :
    (remaining cs [c.packet]).Perm rest := by
  have hn := (hp.map Carrier.packet).nodup_iff.mp hi
  have no : ∀x∈rest,x.packet≠c.packet := by
    intro x hx he
    exact (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨x,hx,he⟩)
  have hf : remaining rest [c.packet]=rest := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [no x hx]
  have h := hp.filter (fun x => !([c.packet] : List Packet).contains x.packet)
  change (remaining cs [c.packet]).Perm (remaining (c::rest) [c.packet]) at h
  have he : remaining (c::rest) [c.packet]=rest := by
    change List.filter _ (c::rest)=rest
    rw [List.filter_cons]
    simpa only [List.contains_cons,List.contains_nil,beq_self_eq_true,Bool.or_false,
      Bool.not_true,Bool.false_eq_true,ite_false,remaining] using hf
  rw [he] at h
  exact h


/-- Actual drop selects the cached queue occurrence in the supplied ledger.
Only its phase changes; the original rest is fixed by removing its packet id. -/
theorem drop_state {id : SkbId} (hi : CarrierState cs loans w) (hd : w.dev=some d)
    (hp : d.peers[pid]?=some p) (peek : p.rxQueue.peeked=some id)
    (ambient ambient' : Ambient)
    (hr : ((dropRxQueue pid).run w).run ambient=.ok (((),v),ambient')) :
    CarrierState (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ ::
      remaining cs [⟨d.ifindex,id⟩]) loans v := by
  let c : Carrier := ⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩
  have member : c∈cs := queued_carrier hi hd hp peek
  have perm := List.perm_cons_erase member
  have moved := hi.perm perm
  obtain ⟨out,hout,iv,qv,pv⟩ := drop_selection id ambient hd hp peek moved.inventory moved.queues moved.funded
  have eq : out=v := by rw [hr] at hout; cases hout; rfl
  subst out
  have hv : v={w with dev:=some {d with peers:=d.peers.insert pid {p with rxQueue:=p.rxQueue.dropPeeked}}} := by
    have h := hr
    simp [dropRxQueue,getPeer,getDev,setPeer,modifyDev,hd,hp] at h
    exact h.1.symm
  have key : keyView v=keyView w := by
    rw [hv]
    exact keyView_set_peer (p:={p with rxQueue:=p.rxQueue.dropPeeked}) hd hp rfl
  have rx' : rxView v=rxView w := by rw [hv]; simp [rxView,hd]
  have state : CarrierState (selected c::cs.erase c) loans v :=
    ⟨iv,qv,pv,(keyEffect_of_view (allowed:=NoPromotion) key).rxCompatible rx' hi.keys.1,(keyEffect_of_view (allowed := NoPromotion) key).currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩
  exact state.perm (List.Perm.cons _ (remaining_one_perm hi.inventory.distinct perm).symm)

def carrierView (w : WGWorld) := (peerView w,rxView w,keyView w)

theorem CarrierState.view (hi : CarrierState cs loans w) (he : carrierView v=carrierView w) : CarrierState cs loans v := by
  have hp := congrArg Prod.fst he
  have hr := congrArg (fun x=>x.2.1) he
  have hk := congrArg (fun x=>x.2.2) he
  exact ⟨inventory_view hi.inventory hr,queueOwners_view hi.queues hp,protected_view hi.funded hp,
    (keyEffect_of_view (allowed:=NoPromotion) hk).rxCompatible hr hi.keys.1,(keyEffect_of_view (allowed := NoPromotion) hk).currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩

theorem counter_carrierView (kp : KeypairId) (nonce : Nat) : SameView carrierView (counterValidate kp nonce) := by
  intro initial
  let P := fun g => carrierView g = initial
  have getter : Hoare (getKeypair kp) P (fun k g => P g ∧ keyWords g kp = some k.peer) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    obtain ⟨hv,_,d,hd,hk⟩ := KeyTimes.getKeypair_return kp w v k ambient ambient' hr
    subst v
    exact ⟨hi,by simp [keyWords,hd,hk]⟩
  unfold counterValidate
  apply hoare_bind _ _ getter
  intro k
  let Q := fun g => P g ∧ keyWords g kp = some k.peer
  have setter (counter : ReplayCounter) : Preserves Q (setKeypair kp {k with receivingCounter := counter}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    cases hd : w.dev with
    | none => simp [Q,keyWords,hd] at hi
    | some d =>
      cases hr
      have keys : keyWords {w with dev := some {d with keypairs := d.keypairs.insert kp {k with receivingCounter := counter}}} = keyWords w := by
        funext q
        by_cases h : kp = q
        · subst q
          simpa [keyWords,hd] using hi.2.symm
        · simp [keyWords,hd,Std.TreeMap.getElem?_insert,h]
      have cv : carrierView {w with dev := some {d with keypairs := d.keypairs.insert kp {k with receivingCounter := counter}}} = carrierView w := by
        unfold carrierView peerView rxView keyView currentCells
        simp only [hd,Option.map_some,Option.bind_some,keys]
      constructor
      · simpa only [P,hd,Option.map_some] using cv.trans hi.1
      · simpa only [hd,Option.map_some,keys] using hi.2
  apply hoare_consequence (P := Q) (Q := fun _ => Q) ?_ (fun _ h => h) (fun _ _ h => h.1)
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id Q)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem complete_carrierView (pid : PeerId) : SameView carrierView (completeRxQueue pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  unfold completeRxQueue at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,hset⟩ := hr
  obtain ⟨ha,haa,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hget
  subst a; subst aa
  cases hset
  have hc := control_set_same (p := {p with napiScheduled := false}) hd hp rfl
  have he : carrierView {w with dev := some {d with peers := d.peers.insert pid {p with napiScheduled := false}}} = carrierView w :=
    Prod.ext (congrArg (fun x => x.1.1) hc)
      (Prod.ext (congrArg (fun x => x.1.2.1) hc) (control_keyView hc))
  simpa only [hd,Option.map_some] using he

/-- Concrete GRO normal/held batches preserve the product through the actual
Stack callback. The supplied bytes need not retain their already-freed RX cell. -/
theorem groNormalList_stack (initial : WGWorld) (g : GroState) :
    ⦃fun w : World => ⌜StackState initial w.wg⌝⦄ groNormalList (fun xs=>xs.forM Leanux.Env.deliverInner) g
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  unfold groNormalList
  split
  · exact preserves_pure _
  · exact preserves_bind (stackForM_stack initial _) (fun _ => preserves_pure _)

theorem groNormalOne_stack (initial : WGWorld) (g : GroState) (bytes : List UInt8) (segs : Nat) :
    ⦃fun w : World => ⌜StackState initial w.wg⌝⦄ groNormalOne (fun xs=>xs.forM Leanux.Env.deliverInner) g bytes segs
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  unfold groNormalOne
  dsimp only
  split
  · exact groNormalList_stack initial _
  · exact preserves_pure _

theorem groReceive_stack (initial : WGWorld) (g : GroState) (bytes : List UInt8) :
    ⦃fun w : World => ⌜StackState initial w.wg⌝⦄ napiGroReceive (fun xs=>xs.forM Leanux.Env.deliverInner) g bytes
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  unfold napiGroReceive
  split
  · exact groNormalOne_stack initial _ _ _
  · split
    · apply preserves_bind (productAmbient_spec (AmbientM.unsupported _)
        (fun w => StackState initial w.wg) (fun _ _ h => h))
      intro _
      exact preserves_pure _
    · exact preserves_pure _

theorem groFlush_stack (initial : WGWorld) (g : GroState) :
    ⦃fun w : World => ⌜StackState initial w.wg⌝⦄ napiGroFlushAll (fun xs=>xs.forM Leanux.Env.deliverInner) g
    ⦃⇓? _ w => ⌜StackState initial w.wg⌝⦄ := by
  change Preserves (fun w : World => StackState initial w.wg) _
  unfold napiGroFlushAll
  apply preserves_bind
  · apply list_view_spec (fun w : World => w.wg) (StackState initial)
    intro bytes cur
    exact preserves_bind (groNormalOne_stack initial cur bytes 1) (fun _ => preserves_pure _)
  · intro cur
    exact preserves_bind (groNormalList_stack initial _) (fun _ => preserves_pure _)

private theorem native_receipt (a : WG.M α) (w v : World) (x : α)
    (hr : (liftWG a).run w = .ok (x,v)) :
    (a.run w.wg).run w.ambient = .ok ((x,v.wg),v.ambient) := by
  rw [liftWG_run] at hr
  cases hn : (a.run w.wg).run w.ambient with
  | error e => simp [hn,Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y,g⟩,ambient⟩
    simp [hn,Except.map] at hr
    rcases hr with ⟨rfl,rfl⟩
    rfl

namespace PollCarrier
open RxJoint

def packetOfStamp (s : PacketStamp) : Packet := ⟨s.1,s.2-1⟩
def removedPackets (h : List RxJoint.Event) := (removedStamps h).map packetOfStamp
def rest (initial : Ledger) (h : List RxJoint.Event) := remaining initial (removedPackets h)
def Context (front initial : Ledger) (loans : Reservations) (h : List RxJoint.Event) (w : World) :=
  CarrierState (front++rest initial h) loans w.wg
abbrev Ready := Context []

theorem removed_frame (hf : HistoryFrame removedStamp a) (w : World) (h : List RxJoint.Event) :
    removedPackets (runPrefix a w h).2=removedPackets h := congrArg (List.map packetOfStamp) (hf w h)

theorem normal_spec {α : Type} {a : RxJoint.Obs α}
    {P : List RxJoint.Event → World → Prop}
    {Q : α → List RxJoint.Event → World → Prop} (ha : Appends a)
    (hq : ∀ w h x v, P h w → (runPrefix a w h).1=.ok (x,v) → Q x (runPrefix a w h).2 v) :
    PrefixEnsures P (fun _=>True) a Q := by
  intro w h hi
  obtain ⟨s,hs⟩ := ha w h
  refine ⟨s,hs,True.intro,?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => trivial
  | ok out => exact hq w h out.1 out.2 hi hr

theorem projected_erases (hp : ProjectsPrefix rho p a b) (he : ErasesTo q b original) :
    ErasesTo (q ∘ p) a original := by
  intro w h
  have hh := congrArg Prod.fst (hp w h)
  rw [←he w (h.filterMap rho),hh]
  cases (runPrefix a w h).1 <;> rfl

theorem context_observed (a : Obs α) (original : Leanux.M β) (p : α→β)
    (ha : Appends a) (he : ErasesTo p a original) (hf : HistoryFrame removedStamp a)
    (hs : ∀ cs loans w x v, CarrierState cs loans w.wg → original.run w=.ok (x,v) → CarrierState cs loans v.wg)
    (front initial : Ledger) (loans : Reservations) :
    PrefixPreserves (Context front initial loans) (fun _=>True) a := by
  apply normal_spec ha
  intro w h x v hi hr
  have ho : original.run w=.ok (p x,v) := by rw [←he w h,hr]; rfl
  have out := hs _ loans w _ v hi ho
  change CarrierState (front++remaining initial (removedPackets (runPrefix a w h).2)) loans v.wg
  rw [removed_frame hf]
  exact out

theorem context_lift (front initial : Ledger) (loans : Reservations) (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (liftPrefix a) :=
  context_observed _ a id (Appends.lift a) (erasesPrefix_lift a).to_projected (HistoryFrame.lift _ a)
    (fun _ _ _ _ _ hi hr=>hi.kernel (congrArg (fun s : ProductStore43 => s.2.2.2) ((ProjectedAction.iff_run _ _ _).mp ha _ _ _ hr))) _ _ _

theorem context_access (front initial : Ledger) (loans : Reservations) (a : PrefixM LifetimeEvent α)
    (he : ErasesPrefix a original) (hf : SameView (fun w : World => carrierView w.wg) original) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (access a) :=
  context_observed _ original id (access_appends _) (access_erases he).to_projected
    (fun w h=>focusPrefix_other RxJoint.Event.access accessEvent removedStamp (fun _=>rfl) a w h)
    (fun _ _ w x v hi hr=>hi.view ((ProjectedAction.iff_run _ _ _).mp hf w x v hr)) _ _ _

private theorem context_native_access (front initial : Ledger) (loans : Reservations) (a : MixedM α)
    (he : ErasesStatePrefix a original) (hf : SameView carrierView original) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (access (liftWGObserver a)) :=
  context_observed _ (liftWG original) id (access_appends _) (access_erases (liftWGObserver_erases he)).to_projected
    (fun w h=>focusPrefix_other RxJoint.Event.access accessEvent removedStamp (fun _=>rfl) _ w h)
    (fun _ _ w x v hi hr=>hi.view ((ProjectedAction.iff_run_ambient _ _ _).mp hf
      w.wg w.ambient x v.wg v.ambient (native_receipt original w v x hr))) _ _ _

theorem context_receive (front initial : Ledger) (loans : Reservations) (g : Gro) (e : Entry) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (receive g e) := by
  apply context_observed _ _ _ (receive_appends g e)
    (projected_erases (receive_gro g e) (napiGroReceiveTagged_erases g.forget e.tag)) (receive_removed g e)
  intro cs loans w out v hi hr
  have st := (hoare_iff_run _ _ _).mp (groReceive_stack w.wg g.erase e.tag.bytes) w out v ⟨Transfer.refl w.wg,hi.keys⟩ hr
  exact hi.transfer st.1 st.2

theorem context_flush (front initial : Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (flushAll g) := by
  apply context_observed _ _ _ (flushAll_appends g)
    (projected_erases (flushAll_gro g) (napiGroFlushAllTagged_erases g.forget).to_projected) (flushAll_removed g)
  intro cs loans w out v hi hr
  have st := (hoare_iff_run _ _ _).mp (groFlush_stack w.wg g.erase) w out v ⟨Transfer.refl w.wg,hi.keys⟩ hr
  exact hi.transfer st.1 st.2

def AfterPeek (initial : Ledger) (loans : Reservations) (pid : PeerId) (first : Option SkbId)
    (h : List RxJoint.Event) (w : World) := Ready initial loans h w ∧ Peeked pid first w.wg

theorem peek_observed (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (Ready initial loans) (fun _=>True) (access (liftWGObserver (peekAccess pid))) (AfterPeek initial loans pid) := by
  apply normal_spec (access_appends _)
  intro w h first v hi hr
  have ho := (access_erases (liftWGObserver_erases (peekAccess_erases pid)) w h).symm.trans hr
  obtain ⟨hv,hp⟩ := peek_state pid hi w.ambient v.ambient (native_receipt _ w v first ho)
  refine ⟨?_,hp⟩
  have frame : HistoryFrame removedStamp (access (liftWGObserver (peekAccess pid))) :=
    fun w h=>focusPrefix_other RxJoint.Event.access accessEvent removedStamp (fun _=>rfl) _ w h
  change CarrierState ([]++remaining initial (removedPackets (runPrefix _ w h).2)) loans v.wg
  rw [removed_frame frame]
  exact hv

theorem ready_kernel (first : Option SkbId) : SameWGStore
    (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  intro initial
  let P := fun g => wgStoreView g = initial
  have getter (id : SkbId) : Preserves P (getRxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient pkt v ambient' hi hr
    obtain ⟨hv,_,_⟩ := Packets.getRxSkb_current id w v pkt ambient ambient' hr
    simpa only [hv] using hi
  change Preserves P _
  unfold WG.andM
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head getRxSkb; exact getter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem ready_observed (initial : Ledger) (loans : Reservations) (pid : PeerId) (first : Option SkbId) :
    PrefixPreserves (AfterPeek initial loans pid first) (fun _=>True) (access (liftWGObserver (readyAccess first))) := by
  apply normal_spec (access_appends _)
  intro w h out v hi hr
  have ho := (access_erases (liftWGObserver_erases (readyAccess_erases first)) w h).symm.trans hr
  have hk := (ProjectedAction.iff_run_ambient _ _ _).mp (ready_kernel first)
    w.wg w.ambient out v.wg v.ambient (native_receipt _ w v out ho)
  have frame : HistoryFrame removedStamp (access (liftWGObserver (readyAccess first))) :=
    fun w h=>focusPrefix_other RxJoint.Event.access accessEvent removedStamp (fun _=>rfl) _ w h
  refine ⟨?_,?_⟩
  · change CarrierState ([]++remaining initial (removedPackets (runPrefix _ w h).2)) loans v.wg
    rw [removed_frame frame]
    exact hi.1.kernel hk
  · have hd : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev hk
    simpa only [Peeked,hd] using hi.2

def Captured (initial : Ledger) (loans : Reservations) (pid skb : Nat) (out : RxPacket×PacketStamp)
    (h : List RxJoint.Event) (w : World) :=
  AfterPeek initial loans pid (some skb) h w ∧ RxDisposition.SelectedAt skb out.2 out.1 w

theorem capture_observed (initial : Ledger) (loans : Reservations) (pid skb : Nat) :
    PrefixEnsures (AfterPeek initial loans pid (some skb)) (fun _=>True) (capture skb) (Captured initial loans pid skb) := by
  apply normal_spec (capture_appends skb)
  intro w h out v hi hr
  obtain ⟨hv,selected⟩ := RxDisposition.capture_selected skb w v h out.1 out.2 hr
  subst v
  refine ⟨⟨?_,hi.2⟩,selected⟩
  have frame : HistoryFrame removedStamp (capture skb) := by
    intro w h
    rw [capture_run]
    cases (liftWG (getRxSkb skb)).run w <;> simp [removedStamp,List.filterMap_append]
  change CarrierState ([]++remaining initial (removedPackets (runPrefix _ w h).2)) loans w.wg
  rw [removed_frame frame]
  exact hi.1

def Selected (stamp : PacketStamp) (o : Owner) : Carrier := ⟨packetOfStamp stamp,o,.selected⟩
def Bare (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (h : List RxJoint.Event) (w : World) : Prop :=
  ∃ o,o.slot=pid ∧ stamp.2=skb+1 ∧ Context [Selected stamp o] initial loans h w
def Live (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (h : List RxJoint.Event) (w : World) :=
  Bare initial loans pid skb stamp h w ∧ RxDisposition.SelectedAt skb stamp pkt w

theorem access_removed (a : PrefixM LifetimeEvent α) : HistoryFrame removedStamp (access a) :=
  fun w h=>focusPrefix_other RxJoint.Event.access accessEvent removedStamp (fun _=>rfl) a w h

theorem drop_observed (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (Captured initial loans pid skb (pkt,stamp)) (fun _=>True)
      (drop pid n skb stamp) (fun _=>Live initial loans pid skb stamp pkt) := by
  apply normal_spec (Appends.bind (access_appends _) (fun _=>emit_appends _))
  intro w h out v hi hr
  simp only [runPrefix_bind] at hr ⊢
  cases ha : runPrefix (access (liftWGObserver (rxDropPeekedPrefix pid))) w h with
  | mk result t => cases result with
    | error e => simp [ha] at hr
    | ok result =>
      rcases result with ⟨u,a⟩; cases u
      simp only [ha,runPrefix_emit,Except.ok.injEq,Prod.mk.injEq] at hr
      have av := hr.2
      subst a
      simp only [runPrefix_emit]
      obtain ⟨d,p,hd,hp,hpeek⟩ := hi.1.2
      have stampEq : stamp=(d.ifindex,skb+1) := by
        simpa [Lifetimes.packetStamp,hd] using hi.2.1.symm
      have original : (liftWG (dropRxQueue pid)).run w=.ok ((),v) := by
        exact (access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)) w h).symm.trans (congrArg Prod.fst ha)
      have out := drop_state hi.1.1 hd hp hpeek w.ambient v.ambient (native_receipt _ w v () original)
      have ht : removedPackets t=removedPackets h := by
        simpa only [ha] using removed_frame (access_removed (liftWGObserver (rxDropPeekedPrefix pid))) w h
      have hremoved : removedPackets (t++[RxJoint.Event.removed n skb stamp])=
          removedPackets h++[⟨d.ifindex,skb⟩] := by
        simpa [removedPackets,removedStamps,List.filterMap_append,removedStamp,stampEq,packetOfStamp] using
          congrArg (fun xs=>xs++[⟨d.ifindex,skb⟩]) ht
      refine ⟨⟨⟨d.ifindex,pid,p.internalId⟩,rfl,by simp [stampEq],?_⟩,
        RxDisposition.selected_transport skb stamp pkt w v ((ProjectedAction.iff_run _ _ _).mp (RxDisposition.drop_rxStore pid) w () v original) hi.2⟩
      change CarrierState (Selected stamp _::remaining initial (removedPackets (t++[.removed n skb stamp]))) loans v.wg
      rw [hremoved,remaining_append]
      simpa only [Selected,packetOfStamp,stampEq,Nat.add_sub_cancel,Ready,Context,List.nil_append,rest] using out

theorem bare_observed (a : Obs α) (ha : Appends a)
    (hs : ∀ front initial loans, PrefixPreserves (Context front initial loans) (fun _=>True) a) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _=>True) a := by
  apply normal_spec ha
  intro w h x v ⟨o,ho,hstamp,hi⟩ hr
  obtain ⟨s,hh,_,out⟩ := hs [Selected stamp o] initial loans w h hi
  exact ⟨o,ho,hstamp,by simpa only [hr] using out⟩

theorem live_observed (a : Obs α) (original : Leanux.M α) (ha : Appends a)
    (he : ErasesPrefix a original)
    (hs : ∀ front initial loans, PrefixPreserves (Context front initial loans) (fun _=>True) a)
    (rx : SameView RxDisposition.rxStore original) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True) a := by
  apply normal_spec ha
  intro w h x v hi hr
  obtain ⟨s,hh,_,out⟩ := bare_observed a ha hs w h hi.1
  exact ⟨by simpa only [hr] using out,
    RxDisposition.selected_transport skb stamp pkt w v ((ProjectedAction.iff_run _ _ _).mp rx w x v ((he w h).symm.trans hr)) hi.2⟩

theorem context_receipt (a : Obs α) (f : RunWitness α→RxJoint.Event)
    (ha : PrefixPreserves (Context front initial loans) (fun _=>True) a)
    (hf : ∀r,removedStamp (f r)=none) :
    PrefixPreserves (Context front initial loans) (fun _=>True) (receiptObserved a f) := by
  intro w h hi
  obtain ⟨s,hs,_,out⟩ := ha w h hi
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix a w h with
  | mk result t => cases result with
    | error e => exact ⟨s,by simpa only [hr] using hs,True.intro,True.intro⟩
    | ok result =>
      rcases result with ⟨x,v⟩
      refine ⟨s++[f ⟨x,w,v⟩],by simp only [hr] at hs; simp [hs,List.append_assoc],True.intro,?_⟩
      change CarrierState (front++remaining initial _) loans v.wg
      have frame : removedPackets (t++[f ⟨x,w,v⟩])=removedPackets t := by
        simp [removedPackets,removedStamps,List.filterMap_append,hf]
      rw [frame]
      simpa only [hr,Context,rest] using out

theorem live_lift (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True) (liftPrefix a) :=
  live_observed _ _ (Appends.lift _) (erasesPrefix_lift _)
    (fun _ _ _=>context_lift _ _ _ _ ha) (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      have hd := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
        ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)
      change v.wg.dev = w.wg.dev at hd
      unfold RxDisposition.rxStore RxDisposition.nativeRxStore
      rw [hd])

theorem live_receipt_lift (a : Leanux.M α) (ha : SameProductStore a) (f : RunWitness α→RxJoint.Event)
    (hf : ∀r,removedStamp (f r)=none) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True) (receiptObserved (liftPrefix a) f) :=
  live_observed _ _ (Appends.lift _).receiptObserved (RxLink.receipt_erases (erasesPrefix_lift _))
    (fun _ _ _=>context_receipt _ _ (context_lift _ _ _ _ ha) hf)
    (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      have hd := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
        ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)
      change v.wg.dev = w.wg.dev at hd
      unfold RxDisposition.rxStore RxDisposition.nativeRxStore
      rw [hd])

theorem live_counter (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) :=
  live_observed _ _ (access_appends _).receiptObserved
    (RxLink.receipt_erases (access_erases (liftWGObserver_erases (counterValidatePrefix_erases _ _))))
    (fun _ _ _=>context_receipt _ _ (context_native_access _ _ _ _ (counterValidatePrefix_erases _ _) (counter_carrierView _ _)) (fun _=>rfl))
    (RxDisposition.counter_rxStore _ _)

theorem live_state (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (RxJoint.Event.checkedState n skb stamp pkt)) :=
  live_receipt_lift _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h)) _ (fun _=>rfl)

theorem live_endpoint (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Live initial loans pid skb stamp pkt) (fun _=>True)
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (RxJoint.Event.checkedEndpoint n skb stamp pkt)) :=
  live_receipt_lift _ (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _ (fun _=>rfl)

theorem consume_observed (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer=pid) :
    PrefixEnsures (Live initial loans pid skb stamp pkt) (fun _=>True)
      (consume pid n skb stamp pkt ep) (fun _=>Bare initial loans pid skb stamp) := by
  apply normal_spec (consume_appends _ _ _ _ _ _)
  intro w h result v hi hr
  have frame := removed_frame (consume_removed pid n skb stamp pkt ep) w h
  rcases hi.1 with ⟨o,ho,hs,st⟩
  have hpacket : packetAt w.wg (packetOfStamp stamp)=some pkt := by
    rcases hi.2 with ⟨he,hp⟩
    unfold packetAt packetOfStamp Lifetimes.packetStamp at *
    cases hd : w.wg.dev with
    | none => simp [RxDisposition.rxStore,RxDisposition.nativeRxStore,hd] at hp
    | some d => simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,hd,←he] using hp
  rw [consume_run] at hr
  cases ha : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t => cases result with
    | error e => simp [ha] at hr
    | ok out =>
      rcases out with ⟨out,a⟩
      have original := (access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans (congrArg Prod.fst ha)
      have state := consume_state (c:=Selected stamp o) st hpacket guard w.ambient a.ambient (native_receipt _ w a out original)
      cases out <;> simp only [ha,Except.ok.injEq,Prod.mk.injEq] at hr
      all_goals obtain ⟨_,av⟩ := hr; subst a
      all_goals refine ⟨o,ho,hs,?_⟩
      all_goals change CarrierState (_++remaining initial _) loans v.wg
      all_goals rw [frame]; exact state

theorem bare_receive (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (g : Gro) (e : Entry) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _=>True) (receive g e) :=
  bare_observed _ (receive_appends _ _) (fun _ _ _=>context_receive _ _ _ _ _)

theorem bare_option (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (g : Gro) (out : Option Entry) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _=>True)
      (forIn out.toList g (fun e cur=>do let next←receive cur e; pure (.yield next))) := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
  | some e =>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure] using
      bare_receive initial loans pid skb stamp g e

theorem cleanup_observed (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) :
    PrefixEnsures (Bare initial loans pid skb stamp) (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb)))
      (fun _=>Ready initial loans) := by
  let a : Obs Unit := do
    access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
    access (liftWGObserver (peerPutMixed (some pid)))
    _←liftPrefix (branch .rxPollFree flag)
    access (liftWGObserver (freeRxSkbPrefix skb))
  have he : ErasesPrefix a (liftWG (cleanup skb pkt flag)) := by
    rw [cleanup_poll_guard skb pkt pid flag guard]
    simp only [liftWG_bind]
    exact erasesPrefix_bind (access_erases (liftWGObserver_erases (keypairPutPrefix_erases _ _))) (fun _=>
      erasesPrefix_bind (access_erases (liftWGObserver_erases (peerPutMixed_erases _))) (fun _=>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _=>access_erases (liftWGObserver_erases (freeRxSkbPrefix_erases _)))))
  have ha : Appends a := (access_appends _).bind (fun _=>
    (access_appends _).bind (fun _=>(Appends.lift _).bind (fun _=>access_appends _)))
  have hf : HistoryFrame removedStamp a := (access_removed _).bind (fun _=>
    (access_removed _).bind (fun _=>(HistoryFrame.lift _ _).bind (fun _=>access_removed _)))
  apply normal_spec ha
  intro w h out v ⟨o,ho,hs,hi⟩ hr
  cases out
  have original : (liftWG (cleanup skb pkt flag)).run w=.ok ((),v) := (he w h).symm.trans hr
  have slot : (Selected stamp o).packet.slot=skb := by simp [Selected,packetOfStamp,hs]
  have out := selected_cleanup (c:=Selected stamp o) hi rfl (guard.trans ho.symm) w.ambient v.ambient (slot ▸ native_receipt _ w v () original)
  change CarrierState ([]++remaining initial (removedPackets (runPrefix a w h).2)) loans v.wg
  rw [removed_frame hf]
  exact out.1

theorem cleanup_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) (tail : Obs α)
    (hf : PrefixEnsures (Ready initial loans) (fun _=>True) tail Q) :
    PrefixEnsures (Bare initial loans pid skb stamp) (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q := by
  simpa only [bind_assoc] using PrefixEnsures.bind
    (cleanup_observed initial loans pid skb stamp pkt flag guard) (fun u=>by cases u; exact hf)

theorem cleanup_live_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (flag : Bool) (guard : pkt.peer=pid) (tail : Obs α)
    (hf : PrefixEnsures (Ready initial loans) (fun _=>True) tail Q) :
    PrefixEnsures (Live initial loans pid skb stamp pkt) (fun _=>True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _←liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q :=
  (cleanup_bind initial loans pid skb stamp pkt flag guard tail hf).consequence
    (fun _ _ hi=>hi.1) (fun _ _ _ hi=>hi)

theorem keep_bind (a : Obs α) (f : α→Obs β)
    (ha : PrefixPreserves I (fun _=>True) a)
    (hf : ∀x,PrefixEnsures I (fun _=>True) (f x) Q) :
    PrefixEnsures I (fun _=>True) (a >>= f) Q := PrefixEnsures.bind ha hf

theorem stop_bind (a : Leanux.M Unit) (ha : ∀w,∃e,a.run w=.error e) (f : Unit→Obs α) :
    PrefixEnsures P (fun _=>True) (liftPrefix a >>= f) Q := by
  intro w h hi
  obtain ⟨e,he⟩ := ha w
  simp only [runPrefix_bind,runPrefix_lift,he]
  exact ⟨[],by simp,True.intro,True.intro⟩

macro "carrier_step" : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
         | exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
         | exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi.1))
    | (rx_phase_head plain invariant; apply stop_bind (invariant _) (fun _=>⟨_,rfl⟩))
    | (rx_phase_head plain unsupported; apply stop_bind (unsupported _) (fun _=>⟨_,rfl⟩))
    | (rx_phase_head plain peekAccess; apply PrefixEnsures.bind (peek_observed _ _ _))
    | (rx_phase_head plain readyAccess; apply keep_bind _ _ (ready_observed _ _ _ _))
    | (rx_phase_head plain capture; apply PrefixEnsures.bind (capture_observed _ _ _ _))
    | (rx_phase_head plain drop; apply PrefixEnsures.bind (drop_observed _ _ _ _ _ _ _))
    | (rx_phase_head plain consume; apply PrefixEnsures.bind (consume_observed _ _ _ _ _ _ _ _ (by simp_all)))
    | (rx_phase_head plain ForIn.forIn; apply keep_bind _ _ (bare_option _ _ _ _ _ _ _))
    | (rx_phase_head plain keypairPutPrefix
       first
         | apply cleanup_live_bind _ _ _ _ _ _ _ (by simp_all)
         | apply cleanup_bind _ _ _ _ _ _ _ (by simp_all))
    | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ (live_counter _ _ _ _))
    | (rx_phase_head receipt branch; apply keep_bind _ _ (live_state _ _ _ _))
    | (rx_phase_head receipt endpointFromSkb; apply keep_bind _ _ (live_endpoint _ _ _ _))
    | (rx_phase_head plain branch
       first
         | apply keep_bind _ _ (live_lift _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h)))
         | apply keep_bind _ _ (context_lift _ _ _ _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))))
    | (rx_phase_head plain flushAll; apply keep_bind _ _ (context_flush _ _ _ _))
    | (rx_phase_head plain completeAccess; apply keep_bind _ _ (context_native_access _ _ _ _ (completeAccess_erases _) (complete_carrierView _)))
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | rx_phase_intro
    | rx_phase_match
    | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem poll_tail (initial : Ledger) (loans : Reservations) (pid : PeerId) (budget : Nat)
    (acc : Nat×Gro×Bool) :
    PrefixPreserves (Ready initial loans) (fun _=>True)
      (do
        if !acc.2.2 && acc.1<budget then liftPrefix (invariant "the rx_queue did not drain")
        if ←liftPrefix (branch .rxPollComplete (acc.1<budget)) then
          access (liftWGObserver (completeAccess pid))
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1) := by
  change PrefixEnsures (Ready initial loans) (fun _=>True) _ (fun _=>Ready initial loans)
  carrier_step

/-- Normal source execution transports the same ledger, selecting at actual
queue removal and paying/freeing before removing a carrier from the invariant.
No peer-survival or callback-totality assumption is made. -/
theorem poll_state (initial : Ledger) (loans : Reservations) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Ready initial loans) (fun _=>True) (poll pid budget) := by
  unfold poll
  apply keep_bind _ _ (context_lift [] initial loans _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h)))
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
  · apply PrefixEnsures.bind (Q:=fun _ : Nat×Gro×Bool=>Ready initial loans)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0,({}:Gro),false) _
        (fun _ : Nat×Gro×Bool=>Ready initial loans) (fun _=>True) (fun _ _ _ _=>True.intro))
      intro index acc
      carrier_step
    · intro acc
      exact poll_tail initial loans pid budget acc

@[simp] theorem seed_removedPackets (prior : List LifetimeEvent) : removedPackets (seed prior)=[] := by
  unfold removedPackets removedStamps seed
  rw [filterMap_disjoint RxJoint.Event.access removedStamp (fun _=>rfl)]
  rfl

theorem remaining_inventory_gone (hi : Inventory (remaining initial removed) w) (hp : p∈removed) :
    packetAt w p=none := by
  unfold packetAt
  cases hd : w.dev with
  | none => rfl
  | some d =>
    change (if d.ifindex != p.epoch then none else d.rxSkbs[p.slot]?)=none
    split
    · rfl
    · rename_i epoch
      have he : d.ifindex=p.epoch := by simpa using epoch
      cases hs : d.rxSkbs[p.slot]? with
      | none => rfl
      | some pkt =>
        obtain ⟨c,hc,hpacket⟩ := hi.complete d p.slot pkt hd hs
        have no := (List.mem_filter.mp hc).2
        have hsame : c.packet=p := by cases p; simpa [he] using hpacket
        simp [hsame,hp] at no

/-- The public cut starts with only prior lifetime accesses. Hence every
subtracted allocation identity comes from this poll's actual fresh suffix.
Uncrypted queued heads and every other unremoved carrier remain in the same
original ledger, with their exact phase/owner and funded reservations. -/
theorem poll_normal (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (hi : CarrierState initial loans w.wg) (hr : (WG.rxPoll pid budget (fun packets=>packets.forM Leanux.Env.deliverInner)).run w=.ok (n,v)) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    CarrierState (remaining initial (removedPackets h)) loans v.wg ∧
      ∀p∈removedPackets h,packetAt v.wg p=none := by
  have joint : (runPrefix (poll pid budget) w (seed prior)).1=.ok (n,v) :=
    (poll_erases pid budget w (seed prior)).trans hr
  have start : Ready initial loans (seed prior) w := by
    have empty : remaining initial []=initial := List.filter_eq_self.mpr (fun _ _=>rfl)
    simpa [Ready,Context,rest,empty] using hi
  obtain ⟨s,hs,_,out⟩ := poll_state initial loans pid budget w (seed prior) start
  have state : CarrierState (remaining initial (removedPackets (runPrefix (poll pid budget) w (seed prior)).2)) loans v.wg := by
    simpa only [joint,Ready,Context,rest,List.nil_append] using out
  exact ⟨state,fun p hp=>remaining_inventory_gone state.inventory hp⟩

end PollCarrier

end Leanux.Proofs.WG.Queues.RxCredits
