import Leanux.Proofs.WG.Queues.RxIngressCarrier

/-! Stable RX boundaries relate the logical ring to the same carrier ledger.
Physical stale slots remain governed by the separate initialized ring model.
A cold nonempty peer queue must have an uncrypted head; ready tails can wait
behind that head. None of these definitions asserts initialized reachability. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
set_option pp.structureInstances false

/-- The same physical ring predicate projected to its native WG state. -/
def NativeRxInv (epoch : Nat) (initial : PtrRing SkbId) (h : List RxRing.Event) (w : WGWorld) : Prop :=
  ∃ ring, RxRing.Refines initial h ring ∧ RxRing.nativeCell w = some (epoch,ring)

def uncrypted (cs : Ledger) (w : WGWorld) : List Packet :=
  (cs.filter fun c => (packetAt w c.packet).any (fun p => p.state == .uncrypted)).map (·.packet)

structure StableRx (cs : Ledger) (w : WGWorld) : Prop where
  queued : ∀ c ∈ cs, c.phase=.queued
  ring : ∀ d, w.dev=some d →
    (d.decryptQueue.items.map fun id => Packet.mk d.ifindex id).Perm (uncrypted cs w)
  cold : ∀ (d : Device) (pid : PeerId) (p : Peer) (id : SkbId), w.dev=some d → d.peers[pid]?=some p →
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
    (physical : NativeRxInv epoch (PtrRing.init n) h w)
    (empty : ∀ d, w.dev=some d → d.decryptQueue.empty=true)
    (cold : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev=some d → d.peers[pid]?=some p → p.napiScheduled=false) :
    cs=[] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket), w.dev=some d → d.rxSkbs[id]?≠some pkt := by
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
      simp_all
    have owner : c.owner=⟨d.ifindex,c.owner.slot,p.internalId⟩ := by
      cases he : c.owner
      simp_all
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
    have ringEq : ring=d.decryptQueue := by simpa [RxRing.nativeCell,hd] using congrArg (Option.map Prod.snd) hcell.symm
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
def stableView (w : WGWorld) :=
  (RxRing.nativeCell w, rxView w, fun pid : PeerId =>
    (w.dev.bind fun d => d.peers[pid]?).map fun p => (p.rxQueue,p.napiScheduled))

theorem StableRx.view (hs : StableRx cs w) (hv : stableView v=stableView w) : StableRx cs v := by
  have ring : RxRing.nativeCell v=RxRing.nativeCell w := congrArg Prod.fst hv
  have rx : rxView v=rxView w := congrArg (fun x => x.2.1) hv
  have peers : (fun (pid : PeerId) => (v.dev.bind fun d => d.peers[pid]?).map fun (p : Peer) => (p.rxQueue,p.napiScheduled)) =
      (fun (pid : PeerId) => (w.dev.bind fun d => d.peers[pid]?).map fun (p : Peer) => (p.rxQueue,p.napiScheduled)) := congrArg (fun x => x.2.2) hv
  have packets : ∀p,packetAt v p=packetAt w p := fun p => by
    have epoch := congrArg Prod.fst rx
    have slots := congrFun (congrArg Prod.snd rx) p.slot
    cases h₁:v.dev <;> cases h₂:w.dev <;> simp_all [rxView,packetAt]
  refine ⟨hs.queued,?_,?_⟩
  · intro d hd
    have old : ∃e,w.dev=some e ∧ e.ifindex=d.ifindex ∧ e.decryptQueue=d.decryptQueue := by
      cases hw:w.dev <;> simp_all [stableView,RxRing.nativeCell]
    obtain ⟨e,he,ep,hq⟩ := old
    have perm := hs.ring e he
    simpa [ep,hq,uncrypted,packets] using perm
  · intro d pid p id hd hp cold head
    have old : ∃e q,w.dev=some e ∧ e.peers[pid]?=some q ∧ q.rxQueue=p.rxQueue ∧ q.napiScheduled=p.napiScheduled := by
      have eq := congrFun peers pid
      simp only [hd,Option.bind_some,hp,Option.map_some] at eq
      obtain ⟨q,hq,hfields⟩ := Option.map_eq_some_iff.mp eq.symm
      obtain ⟨e,he,hep⟩ := Option.bind_eq_some_iff.mp hq
      exact ⟨e,q,he,hep,(congrArg Prod.fst hfields),(congrArg Prod.snd hfields)⟩
    obtain ⟨e,q,he,hq,queue,napi⟩ := old
    obtain ⟨pkt,hpkt,state⟩ := hs.cold e pid q id he hq (napi.trans cold) (queue ▸ head)
    have slots := congrFun (congrArg Prod.snd rx) id
    exact ⟨pkt,by simpa [rxView,hd,he,hpkt] using slots,state⟩

theorem stableView_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => stableView (project w)) a :=
  ha.of_factor (fun store : WGStoreView =>
    (store.dev.map (fun d => (d.ifindex,d.decryptQueue)),
      (store.dev.map (·.ifindex),fun id : SkbId => store.dev.bind fun d => d.rxSkbs[id]?),
      fun pid : PeerId => (store.dev.bind fun d => d.peers[pid]?).map fun p => (p.rxQueue,p.napiScheduled))) _
    (fun _ => rfl)

theorem stable_peerGetMaybeZero (id : Option PeerId) : SameView stableView (peerGetMaybeZero id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec id (wgStoreView w)) w ambient result v ambient' rfl hr).2
  cases result with
  | none =>
    have hd := congrArg WGStoreView.dev hb
    change v.dev = w.dev at hd
    unfold stableView RxRing.nativeCell rxView
    rw [hd]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := hb
    have dev := congrArg WGStoreView.dev hv
    change v.dev = some _ at dev
    change w.dev = some d at hd
    simp only [stableView,RxRing.nativeCell,rxView,dev,hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext q
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem stable_ownerStore (owner : IndexOwner) (word : Option PeerId) : SameView stableView (owner.setPeerWord word) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  cases owner with
  | handshake pid =>
    unfold IndexOwner.setPeerWord at hr
    rw [MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨p,a,aa,hg,hs⟩ := hr
    obtain ⟨ha,haa,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hg
    subst a
    subst aa
    cases hs
    simp only [stableView,RxRing.nativeCell,rxView,hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext q
    by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]
  | keypair kid =>
    obtain ⟨d,k,hd,hk,hv,_⟩ := Origins.keypair_word_store kid word w v ambient ambient' hr
    rw [hv]
    simp only [stableView,RxRing.nativeCell,rxView,CounterWindow.store,hd,Option.map_some,Option.bind_some]

theorem stable_acquireOwner (owner : IndexOwner) : SameView stableView (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  have read : SameView stableView owner.peerWord := by
    intro s
    exact indexOwner_peerWord_preserves owner (fun w => stableView w=s)
  exact read.bind fun word =>
    (stable_peerGetMaybeZero word).bind fun result =>
      (stable_ownerStore owner result).bind fun _ => SameView.pure _ _

theorem stable_indexLookup (kinds : List IndexKind) (index : Nat) : SameView stableView (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  apply SameView.of_wp
  intro s
  let P := fun w => stableView w=s
  have ha := fun owner => (stable_acquireOwner owner).wp (fun t => t=s)
  have hb : Preserves P (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa [P,stableView,RxRing.nativeCell,rxView,hd] using hg
  have branchSpec (decision : Decision) (value : Bool) :
      Preserves P (branch decision value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have stop {α : Type} (why : String) : Preserves P (invariant why : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant why) P
  unfold Affiliation.indexLookupSource
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head branch; exact branchSpec _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hb)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem stable_keypairGet (id : Option KeypairId) : SameView stableView (keypairGet id) := by
  intro initial
  let P := fun g => stableView g=initial
  have getter (id) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    simpa only [(KeyTimes.getKeypair_return id w v k ambient ambient' hr).1] using hi
  have setter (id) (k : Keypair) : Preserves P (setKeypair id k) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,stableView,RxRing.nativeCell,rxView,hd] using hi
  unfold keypairGet refcountIncNotZero
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter _)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem stable_keypairPut (id : Option KeypairId) (now : Bool) : SameView stableView (keypairPut id now) := by
  intro initial
  let P := fun g => stableView g=initial
  have getter (id) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    simpa only [(KeyTimes.getKeypair_return id w v k ambient ambient' hr).1] using hi
  have setter (id) (k : Keypair) : Preserves P (setKeypair id k) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,stableView,RxRing.nativeCell,rxView,hd] using hi
  have deref := fun owner => indexOwner_peerDeref_preserves owner P
  have index (a : IndexM Unit) : Preserves P (liftIndex a) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa [P,stableView,RxRing.nativeCell,rxView,hd] using hg
  have erase (id) : Preserves P (modifyDev fun d => {d with keypairs := d.keypairs.erase id}) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    cases hd : w.dev <;> simpa [P,stableView,RxRing.nativeCell,rxView,hd] using hi
  unfold keypairPut refcountDecAndTest
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter _)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head IndexOwner.peerDeref; exact deref _)
    | (index_material_head indexRemove; exact index _)
    | (index_material_head liftIndex; exact index _)
    | (index_material_head MonadLift.monadLift; with_reducible exact index _)
    | (index_material_head MonadLiftT.monadLift; with_reducible exact index _)
    | (index_material_head monadLift; with_reducible exact index _)
    | (index_material_head modifyDev; exact erase _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)
  all_goals exact index _

theorem StableRx.peerKernel (hs : StableRx cs w) (hd : w.dev=some d)
    (peers : Std.TreeMap PeerId Peer compare)
    (back : ∀(pid : PeerId) (p : Peer),peers[pid]?=some p → ∃q : Peer,d.peers[pid]?=some q ∧
      q.rxQueue=p.rxQueue ∧ q.napiScheduled=p.napiScheduled) :
    StableRx cs {w with dev:=some {d with peers}} := by
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

theorem stable_payment_effect (hd : w.dev=some d) (hp : d.peers[pid]?=some p)
    (ambient ambient' : Ambient)
    (hr : ((peerPut (some pid)).run w).run ambient=.ok (((),v),ambient')) :
    stableView v=stableView (paymentState w d pid p) := by
  have positive := (peerPut_effect pid w v d p ambient ambient' hd hp hr).1
  have nonzero : p.refcount ≠ 0 := by omega
  have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
  by_cases final : p.refcount = 1
  all_goals
    simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
      refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
      hl, liftIndex_run, retirePeerUnits, modifyAmbient,
      CounterWindow.branch_run, CounterWindow.branchCmp_run,
      hd, hp, positive, nonzero, final,
      StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
      CounterWindow.except_ok_bind, CounterWindow.except_pure,
      invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at hr
  all_goals repeat' first | split at hr | contradiction
  all_goals rcases hr with ⟨rfl,rfl⟩
  all_goals simp_all [stableView,RxRing.nativeCell,rxView,paymentState,
    Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase]

theorem StableRx.put (hs : StableRx cs w) (ambient ambient' : Ambient)
    (hr : ((peerPut pid).run w).run ambient=.ok (((),v),ambient')) : StableRx cs v := by
  cases pid with
  | none =>
    simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,
      StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
      CounterWindow.except_pure] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact hs
  | some pid =>
    obtain ⟨d,p,hd,hp⟩ : ∃d p,w.dev=some d ∧ d.peers[pid]?=some p := by
      cases hd:w.dev with
      | none =>
        simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
          getPeer,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind,
          StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
        change Except.error _ = Except.ok (((),v),ambient') at hr
        cases hr
      | some d =>
        cases hp:d.peers[pid]? with
        | none =>
          simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
            getPeer,getDev,hd,hp,invariant,AmbientM.invariant,StateT.run_bind,
            StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
          change Except.error _ = Except.ok (((),v),ambient') at hr
          cases hr
        | some p => exact ⟨d,p,rfl,hp⟩
    apply StableRx.view (w:=paymentState w d pid p) _ (stable_payment_effect hd hp ambient ambient' hr)
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
    (hd : w.dev=some d) (fresh : d.rxSkbs[d.nextSkb]?=none) (pkt : RxPacket) :
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
      simpa [Affiliation.receiveKeyAcquire] using
        (stable_keypairGet (some id)).bind (fun _ => SameView.pure _ _)

theorem admitted_stable_front (hs : StableRx cs w) (hi : Inventory cs w) (hf : Packets.Inv w)
    (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((some ctx,v),ambient')) : StableRx cs v := by
  obtain ⟨entry,a,aa,b,ab,c,ac,peer,d,ad,e,ae,hl,hk,hno,hp,hd,_,hn⟩ :=
    RxOrigin.admission_execution msg src ds ctx w v ambient ambient' hr
  have vb := ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_receiveKey entry) a aa _ b ab hk).trans
    ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_indexLookup [.keypair] (u32le msg 4)) w ambient _ a aa hl)
  have kc : c=b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair false) (fun g => g=b)) b ab false c ac rfl hno
  have kd := (getPeer_normal ctx.packet.peer c d peer ac ad hp).1
  have ke : e=d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g=d)) d ad false e ae rfl hd
  have eb : e=b := ke.trans (kd.trans kc)
  have ve : stableView e=stableView w := by simpa only [eb] using vb
  have ie : Inventory cs e := inventory_view hi (congrArg (fun x => x.2.1) ve)
  have packets := ((ProjectedAction.iff_run_ambient _ _ _).mp (receiveKey_packets entry) a aa _ b ab hk).trans
    ((ProjectedAction.iff_run_ambient _ _ _).mp (indexLookup_packets [.keypair] (u32le msg 4)) w ambient entry a aa hl)
  have pe : Packets.snapshot e=Packets.snapshot w := by simpa only [eb] using packets
  have fe : Packets.Inv e := by simpa only [Packets.Inv,pe] using hf
  obtain ⟨dev,hdev,slot,after,_,_⟩ := RxOrigin.allocation_record ctx.packet ⟨ctx.slot,e,v,ae,ambient'⟩ hn
  change e.dev=some dev at hdev
  change v=Packets.update e _ at after
  rw [after]
  simpa [Packets.update,hdev] using (hs.view ve).allocate ie hdev (Packets.allocation_slots_empty e dev hdev fe).2 ctx.packet

theorem StableRx.kernel (hs : StableRx cs w) (hk : wgStoreView v=wgStoreView w) : StableRx cs v :=
  hs.view (by
    have hd : v.dev=w.dev := congrArg WGStoreView.dev hk
    unfold stableView RxRing.nativeCell rxView
    rw [hd])

theorem stable_enqueue {id : SkbId} {pkt : RxPacket} (hs : StableRx cs w) (hd : w.dev=some d)
    (hp : d.peers[pkt.peer]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (state : pkt.state=.uncrypted) (cp : c.packet=⟨d.ifindex,id⟩)
    (physical : RxRing.Refines (PtrRing.init n) h d.decryptQueue)
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient=.ok ((ret,v),ambient')) :
    if ret=0 then StableRx (enqueued c::cs) v else StableRx cs v := by
  obtain ⟨outcomes,cpu,hv⟩ := enqueue_effect hd hpacket hp ambient ambient' hr
  let v0 : WGWorld := {w with dev:=some (enqueueDevice d id pkt p ret cpu)}
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
    all_goals simp_all [packetAt,v0,enqueueDevice,Std.TreeMap.getElem?_insert]
  have cold : ∀(out : Device) (pid : PeerId) (q : Peer) (sid : SkbId),v0.dev=some out → out.peers[pid]?=some q →
      q.napiScheduled=false → q.rxQueue.all.head?=some sid →
      ∃stored : RxPacket,out.rxSkbs[sid]?=some stored ∧ stored.state=.uncrypted := by
    intro out pid q sid hout hq hnapi hhead
    have eq : out=enqueueDevice d id pkt p ret cpu := Option.some.inj hout.symm
    subst out
    have store : ∀sid : SkbId,(enqueueDevice d id pkt p ret cpu).rxSkbs[sid]?=d.rxSkbs[sid]? := by
      intro j
      by_cases he:id=j <;> simp_all [enqueueDevice,Std.TreeMap.getElem?_insert]
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
      have free : d.decryptQueue.full=false := RxRing.enqueue_free (deviceIndex:=d.ifindex) (r:=d.decryptQueue) id (by simp [RxRing.nativeCell,hd]) (zero ▸ hr)
      have contents := ring_produce_items physical free id
      have newlist : uncrypted (enqueued c::cs) v0=c.packet::uncrypted cs w := by
        have hc : packetAt v0 c.packet=some pkt := (packets c).trans (by simp [cp,packetAt,hd,hpacket])
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


theorem admitted_none_stable (hs : StableRx cs w) (ambient ambient' : Ambient)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((none,v),ambient')) : StableRx cs v := by
  rw [RxOrigin.admitSource_factor] at hr
  obtain ⟨entry,a,aa,hl,acquired,b,ab,hk,noKey,c,ac,hn,rest⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using hr)
  rcases acquired with ⟨kp,pid⟩
  have front := hs.view (((ProjectedAction.iff_run_ambient _ _ _).mp (stable_receiveKey entry) a aa _ b ab hk).trans
    ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_indexLookup [.keypair] (u32le msg 4)) w ambient _ a aa hl))
  have cb : c=b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair kp.isNone) (fun g => g=b)) b ab noKey c ac rfl hn
  have fc : StableRx cs c := cb ▸ front
  cases noKey with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,z,az,hpay,he⟩ := rest
    cases u
    have zv : z=v := (by simpa using he : z=v ∧ az=ambient').1
    exact zv ▸ fc.put ac az hpay
  | false =>
    simp only [Bool.false_eq_true,ite_false] at rest
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
        obtain ⟨peer,d,ad,hread,dead,e,ae,hdead,rest⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using rest)
        have kd := (getPeer_normal pid c d peer ac ad hread).1
        have ke : e=d := (hoare_iff_run_ambient _ _ _).mp
          (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g=d)) d ad dead e ae rfl hdead
        have fe : StableRx cs e := (ke.trans kd) ▸ fc
        cases dead with
        | true =>
          simp only [ite_true,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨u,f,af,hkey,u',g,ag,hpay,he⟩ := rest
          cases u
          cases u'
          have gv : g=v := (by simpa using he : g=v ∧ ag=ambient').1
          exact gv ▸ (fe.view ((ProjectedAction.iff_run_ambient _ _ _).mp
            (stable_keypairPut (some kid) false) e ae () f af hkey)).put af ag hpay
        | false =>
          simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨slot,z,az,ha,bad⟩ := rest
          simp at bad


theorem queued_head {id : SkbId} (hq : QueueOwners cs w) (hd : w.dev=some d) (hp : d.peers[pid]?=some p)
    (head : p.rxQueue.all.head?=some id) : ∃c∈cs,c.packet=⟨d.ifindex,id⟩ ∧
      c.owner=⟨d.ifindex,pid,p.internalId⟩ ∧ c.phase=.queued := by
  have count := hq d pid p id hd hp
  have positive : 0<p.rxQueue.all.count id := by
    cases h:p.rxQueue.all with
    | nil => simp [h] at head
    | cons first rest =>
      have he : first=id := by simpa [h] using head
      subst first
      simp
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
    (hd : w.dev=some d) (hp : d.peers[pid]?=some p) (cp : c.packet=⟨d.ifindex,id⟩)
    (head : p.rxQueue.all.head?=some id) : c.owner=⟨d.ifindex,pid,p.internalId⟩ ∧ c.phase=.queued := by
  obtain ⟨x,hx,hpacket,owner,phase⟩ := queued_head hq hd hp head
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨owner,phase⟩
  · exact (carrier_other hi hx (hpacket.trans cp.symm)).elim

theorem StableRx.free (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (hq : QueueOwners (c::cs) w) (notqueued : c.phase≠.queued)
    (ambient ambient' : Ambient)
    (hr : ((freeRxSkb c.packet.slot).run w).run ambient=.ok (((),v),ambient')) : StableRx cs v := by
  obtain ⟨_,pkt,stored,_⟩ := hi.present c (by simp)
  obtain ⟨d,hd,epoch,hpkt⟩ : ∃d,w.dev=some d ∧ d.ifindex=c.packet.epoch ∧ d.rxSkbs[c.packet.slot]?=some pkt := by
    cases hd:w.dev with
    | none => simp [packetAt,hd] at stored
    | some d =>
      by_cases he:d.ifindex=c.packet.epoch
      · exact ⟨d,rfl,he,by simpa [packetAt,hd,he] using stored⟩
      · simp [packetAt,hd,he] at stored
  have cp : c.packet=⟨d.ifindex,c.packet.slot⟩ := congrArg (fun e => Packet.mk e c.packet.slot) epoch.symm
  rw [Packets.freeRxSkb_run w ambient d c.packet.slot pkt hd hpkt] at hr
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
    (ambient ambient' : Ambient)
    (hr : ((discard c.packet.slot pkt).run w).run ambient=.ok (((),v),ambient')) : StableRx cs v := by
  obtain ⟨u,a,aa,hkey,u,b,ab,hpay,hfree⟩ := (by simpa only [discard,MaterialOrigin.bind_ok_ambient] using hr)
  cases u
  have fr := Prod.mk.inj ((ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame (some pkt.keypair) false) w ambient () a aa hkey)
  have ia := inventory_selected (inventory_view hi.inventory fr.2)
  have sa := selected_protected (protected_view hi.funded fr.1) (by simp [phase,Phase.charged])
  have qa : QueueOwners (selected c::cs) a := by
    intro d pid p id hd hp
    simpa [List.filter_cons,selected,phase] using (queueOwners_view hi.queues fr.1) d pid p id hd hp
  obtain ⟨p,hp,_⟩ := selected_credit sa rfl
  obtain ⟨d,hd,ep,hpeer,stamp⟩ := resident_fields hp
  have payment : ((peerPut (some (selected c).owner.slot)).run a).run aa=.ok (((),b),ab) := by simpa [selected,owner] using hpay
  have ib := inventory_paid (inventory_view ia (peerPut_effect _ a b d p aa ab hd hpeer payment).2.2)
  have qb := selected_payment_queues qa rfl hd hpeer aa ab payment
  have stable := (hs.view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (stable_keypairPut (some pkt.keypair) false) w ambient () a aa hkey)).put aa ab hpay
  exact stable.free ib qb (by simp [paid]) ab ambient' hfree

theorem stable_peerGet (pid : PeerId) : SameView stableView (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hr
  cases u
  obtain ⟨d,p,hd,hp,pos,hv⟩ := peerGet_loan pid w v ambient ambient' hr
  have dev := congrArg WGStoreView.dev hv
  change v.dev = some _ at dev
  change w.dev = some d at hd
  simp only [stableView,RxRing.nativeCell,rxView,dev,hd,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases he : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]


def publicationDevice (d : Device) (id : SkbId) (pkt : RxPacket) (pid : PeerId) (p : Peer) : Device :=
  {d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=.dead},peers:=d.peers.insert pid {p with napiScheduled:=true}}

theorem publicationMiddle_effect {id : SkbId} {pkt : RxPacket}
    (hd : w.dev=some d) (hp : d.peers[pid]?=some p) (hpacket : d.rxSkbs[id]?=some pkt)
    (ambient ambient' : Ambient)
    (hr : ((publicationMiddle pid id .dead).run w).run ambient=.ok (((),v),ambient')) :
    wgStoreView v={wgStoreView w with dev:=some (publicationDevice d id pkt pid p)} := by
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
    have exactSet := Packets.setRxSkb_run w ambient d id pkt (fun q => {q with state:=.dead}) hd hpacket
    rw [hs] at exactSet
    cases exactSet
    cases ht
    simp [wgStoreView,publicationDevice,Packets.update,hd]


theorem stable_publicationMiddle (hs : StableRx cs w) (hi : Inventory (c::cs) w)
    (queues : QueueOwners (c::cs) w) (owner : c.owner.slot=pid)
    (ambient ambient' : Ambient)
    (hr : ((publicationMiddle pid c.packet.slot .dead).run w).run ambient=.ok (((),v),ambient')) :
    StableRx cs v ∧ ∃pkt,packetAt v c.packet=some pkt ∧ pkt.state=.dead := by
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
  have effect := publicationMiddle_effect hd hp hpacket ambient ambient' hr
  let v0 : WGWorld := {w with dev:=some (publicationDevice d c.packet.slot pkt pid p)}
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
  have dev := congrArg WGStoreView.dev effect
  change v.dev=some (publicationDevice d c.packet.slot pkt pid p) at dev
  exact ⟨{pkt with state:=.dead},by simp [packetAt,dev,publicationDevice,epoch],rfl⟩


theorem compatible_peerDeref (hc : KeyCompatible owner kid w)
    (ambient ambient' : Ambient)
    (hr : ((IndexOwner.peerDeref (.keypair kid)).run w).run ambient=.ok ((pid,v),ambient')) : pid=owner := by
  cases hd:w.dev with
  | none =>
    simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,invariant,AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk:d.keypairs[kid]? with
    | none =>
      simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,invariant,AmbientM.invariant] at hr
      cases hr
    | some k =>
      have compatible := hc d k hd hk
      cases hw:k.peer with
      | none =>
        simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,hw,unsupported,AmbientM.unsupported] at hr
        cases hr
      | some q =>
        have eq : q=pid := by
          have h : (q=pid) ∧ w=v ∧ ambient=ambient' := by
            simpa [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,hw,and_assoc] using hr
          exact h.1
        rw [←eq]
        simpa [Affiliation.Compatible,hw] using compatible

theorem peerPut_rxView (pid : Option PeerId) : SameView rxView (peerPut pid) := by
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
        exact keep

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
    (phase : c.phase=.queued) (ambient ambient' : Ambient)
    (hr : ((enqueuePerPeerRx (pure ()) c.packet.slot .dead : WG.M Unit).run w).run ambient=.ok (((),v),ambient')) : StableRx (c::cs) v := by
  rw [publication_factor] at hr
  obtain ⟨pkt,a,aa,hread,pid,b,ab,hderef,u,q,aq,hget,u,e,ae,hmid,hput⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using hr)
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
  obtain ⟨stable,dead,hdead,state⟩ := stable_publicationMiddle stableq iq qq (owner.symm.trans resolved.symm) aq ae hmid
  have keep := (ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_rxView (some pid)) e ae () v ambient' hput
  exact (stable.put ae ambient' hput).add_dead phase ((packetAt_view keep).trans hdead) state


theorem finishAfter_stable (ctx : RxOrigin.Admission) (stable : StableRx cs w)
    (hi : CarrierState (c::cs) loans w) (phase : c.phase=.unpublished)
    (slot : c.packet.slot=ctx.slot) (stored : packetAt w c.packet=some ctx.packet)
    (owner : ctx.packet.peer=c.owner.slot) (state : ctx.packet.state=.uncrypted)
    (physical : NativeRxInv epoch (PtrRing.init n) h w)
    (ambient aAmbient ambient' : Ambient)
    (he : ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient=.ok ((ret,a),aAmbient))
    (ht : ((finishAfter ctx ret).run a).run aAmbient=.ok (((),v),ambient')) :
    if ret=-ENOSPC then StableRx cs v else StableRx (enqueued c::cs) v := by
  have demand : 0<demand (c::cs) loans c.owner := by simp [demand,phase,Phase.charged]; omega
  obtain ⟨p,hp,_⟩ := protected_resident hi.funded demand
  obtain ⟨d,hd,epoch,hpeer,stamp⟩ := resident_fields hp
  have ep : d.ifindex=c.packet.epoch := epoch.trans (hi.inventory.present c (by simp)).1.symm
  have cp : c.packet=⟨d.ifindex,ctx.slot⟩ :=
    (congrArg (fun e => Packet.mk e c.packet.slot) ep.symm).trans (congrArg (Packet.mk d.ifindex) slot)
  have hpacket : d.rxSkbs[ctx.slot]?=some ctx.packet := by simpa [packetAt,hd,ep,slot] using stored
  obtain ⟨ring,href,hcell⟩ := physical
  have ringEq : ring=d.decryptQueue := by simpa [RxRing.nativeCell,hd] using congrArg (Option.map Prod.snd) hcell.symm
  have stableAfter := stable_enqueue (c:=c) stable hd (by simpa [owner] using hpeer) hpacket state cp
    (ringEq ▸ href) ambient aAmbient he
  obtain ⟨choices,ha⟩ := enqueue_state hi phase stored owner ambient aAmbient (by simpa [slot] using he)
  have whole : ((finishSource ctx).run w).run ambient=.ok (((),v),ambient') := by
    simpa only [finish_factor,MaterialOrigin.bind_ok_ambient] using
      (show ∃ret a aa, ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient=.ok ((ret,a),aa) ∧
        ((finishAfter ctx ret).run a).run aa=.ok (((),v),ambient') from ⟨ret,a,aAmbient,he,ht⟩)
  rcases choices with rfl | rfl | rfl
  · have vv : v=a := by
      simp [finishAfter,WG.orM,branch,AmbientM.branch,EPIPE,
        StateT.run_bind,StateT.run_monadLift] at ht
      exact ht.1.symm
    have ready : StableRx (enqueued c::cs) a := by simpa using stableAfter
    simpa [ENOSPC,vv] using ready
  · have run : ((discard c.packet.slot ctx.packet).run a).run (enospcDecisions aAmbient)=.ok (((),v),ambient') := by
      simpa [slot] using (finish_enospc ctx ambient aAmbient he).symm.trans whole
    have initial : CarrierState (c::cs) loans a := by simpa using ha
    have ready : StableRx cs a := by simpa [ENOSPC] using stableAfter
    simpa using stable_discard ready initial phase owner (enospcDecisions aAmbient) ambient' run
  · simp only [finishAfter,MaterialOrigin.bind_ok_ambient] at ht
    obtain ⟨decision,z,az,hbranch,ht⟩ := ht
    change Except.ok ((true,a),CounterWindow.record aAmbient .dataEpipe true) =
      .ok ((decision,z),az) at hbranch
    have dv : decision=true := (congrArg (fun z=>z.1.1) (Except.ok.inj hbranch)).symm
    have zv : z=a := (congrArg (fun z=>z.1.2) (Except.ok.inj hbranch)).symm
    have av : az=CounterWindow.record aAmbient .dataEpipe true := (congrArg Prod.snd (Except.ok.inj hbranch)).symm
    subst decision
    subst z
    rw [av] at ht
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at ht
    obtain ⟨u,b,bb,hpublish,tail⟩ := ht
    cases u
    have initial : CarrierState (enqueued c::cs) loans a := by simpa [ENOSPC,EPIPE] using ha
    have ready : StableRx cs a := by simpa [EPIPE] using stableAfter
    have hb := stable_publication ready initial rfl (CounterWindow.record aAmbient .dataEpipe true) bb
      (by simpa [enqueued,slot] using hpublish)
    have vv : v=b := by
      simp [WG.orM,branch,AmbientM.branch,EPIPE,StateT.run_bind,StateT.run_monadLift] at tail
      exact tail.1.symm
    simpa [ENOSPC,EPIPE,vv] using hb


theorem admit_ring (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    SameView RxRing.nativeCell (RxOrigin.admitSource msg src ds) := by
  intro initial
  let P := fun g=>RxRing.nativeCell g=initial
  have hl := (RxRing.indexLookup_frame [.keypair] (u32le msg 4)).wp (fun t=>t=initial)
  have hg := fun k => (RxRing.keypairGet_frame k).wp (fun t=>t=initial)
  have hp := fun p => (RxRing.getPeer_frame p).wp (fun t=>t=initial)
  have hk := fun k b => (RxRing.keypairPut_frame k b).wp (fun t=>t=initial)
  have hput := fun p => (RxRing.peerPut_frame p).wp (fun t=>t=initial)
  have hn (pkt : RxPacket) : Preserves P (newRxSkb pkt) := by
    unfold newRxSkb
    apply hoare_liftSkb
    intro g d packets hi hd
    simpa [P,RxRing.nativeCell,hd] using hi
  have hnull : Preserves P keypairGetNull := by
    unfold keypairGetNull
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairGetNull true) P)
    intro _
    exact preserves_pure _
  unfold RxOrigin.admitSource RxOrigin.admitWith
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head indexLookup; exact hl)
    | (index_material_head keypairGet; exact hg _)
    | (index_material_head getPeer; exact hp _)
    | (index_material_head keypairPut; exact hk _ _)
    | (index_material_head peerPut; exact hput _)
    | (index_material_head newRxSkb; exact hn _)
    | (index_material_head keypairGetNull; exact hnull)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)
  all_goals exact hnull


/-- The returned ledger is fixed by the actual admission and enqueue outcome.
Both its credit product and its stable ring/head boundary hold; a dead
publication is processable as a drop, not a crypted delivery. -/
def StableConsumption (cs : Ledger) (loans : Reservations) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) (w v : WGWorld) (ambient ambient' : Ambient)
    (r : WGRunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before=w ∧ r.ambientBefore=ambient ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after=v ∧ r.ambientAfter=ambient' ∧ CarrierState cs loans v ∧ StableRx cs v
  | some ctx => ∃ o,
      let c : Carrier := ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩
      CarrierState (c::cs) loans r.after ∧ o.slot=ctx.packet.peer ∧
      KeyWord ctx.packet.keypair ctx.packet.peer r.after ∧
      RxOrigin.Admitted msg src ds ctx w r.after ambient r.ambientAfter ∧
      ∃ ret a aAmbient, ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter=.ok ((ret,a),aAmbient) ∧
        ((finishAfter ctx ret).run a).run aAmbient=.ok (((),v),ambient') ∧
        (ret=0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        (if ret=-ENOSPC then CarrierState cs loans v ∧ StableRx cs v ∧ packetAt v c.packet=none
         else CarrierState (enqueued c::cs) loans v ∧ StableRx (enqueued c::cs) v)

theorem StableConsumption.consumption (h : StableConsumption cs loans msg src ds w v ambient ambient' r) :
    Consumption cs loans msg src ds w v ambient ambient' r := by
  obtain ⟨before,beforeAmbient,valid,rest⟩ := h
  refine ⟨before,beforeAmbient,valid,?_⟩
  cases value:r.value with
  | none =>
    simp only [value] at rest ⊢
    exact ⟨rest.1,rest.2.1,rest.2.2.1⟩
  | some ctx =>
    simp only [value] at rest ⊢
    obtain ⟨o,hi,owner,key,admitted,ret,a,aa,he,ht,choice,result⟩ := rest
    refine ⟨o,hi,owner,key,admitted,ret,a,aa,he,ht,choice,?_⟩
    by_cases hret : ret = -ENOSPC <;> simp_all

/-- Original whole-call normal conservation. The physical premise is the
existing ring journal, and no endpoint WGWorld is assigned to a Stop. -/
theorem consume_stable (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (hs : StableRx cs w) (physical : NativeRxInv epoch (PtrRing.init n) h w)
    (ambient ambient' : Ambient)
    (hr : ((consumeData msg src ds).run w).run ambient=.ok (((),v),ambient')) :
    ∃r,StableConsumption cs loans msg src ds w v ambient ambient' r := by
  obtain ⟨r,before,beforeAmbient,valid,result⟩ := consume_normal hi hf ambient ambient' hr
  refine ⟨r,before,beforeAmbient,valid,?_⟩
  have hfront : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((r.value,r.after),r.ambientAfter) := by
    simpa [WGRunWitness.Valid,before,beforeAmbient] using valid
  cases value:r.value with
  | none =>
    simp only [value] at result ⊢
    have stable : StableRx cs r.after := admitted_none_stable hs ambient r.ambientAfter (by simpa [value] using hfront)
    exact ⟨result.1,result.2.1,result.2.2,result.1 ▸ stable⟩
  | some ctx =>
    simp only [value] at result ⊢
    obtain ⟨o,ha,owner,key,admitted,ret,a,aa,he,ht,choices,endpoint⟩ := result
    have front : ((RxOrigin.admitSource msg src ds).run w).run ambient=.ok ((some ctx,r.after),r.ambientAfter) := by simpa [value] using hfront
    have stable := admitted_stable_front hs hi.inventory hf ambient r.ambientAfter front
    have physicalAfter : NativeRxInv epoch (PtrRing.init n) h r.after := by
      obtain ⟨ring,href,hcell⟩ := physical
      exact ⟨ring,href,((ProjectedAction.iff_run_ambient _ _ _).mp (admit_ring msg src ds) w ambient _ r.after r.ambientAfter front).trans hcell⟩
    obtain ⟨_,pkt,hpkt,_⟩ := ha.inventory.present ⟨⟨o.epoch,ctx.slot⟩,o,.unpublished⟩ (by simp)
    have eq : pkt=ctx.packet := admitted_packet ambient r.ambientAfter front hpkt
    subst pkt
    have state : ctx.packet.state=.uncrypted := by
      obtain ⟨entry,b,ab,c,ac,d,ad,peer,e,ae,f,af,hl,hk,hno,hpeer,hdead,packet,alloc⟩ := admitted
      rw [packet]
    have finalStable := finishAfter_stable ctx stable ha rfl rfl hpkt owner.symm state physicalAfter r.ambientAfter aa ambient' he ht
    refine ⟨o,ha,owner,key,admitted,ret,a,aa,he,ht,choices,?_⟩
    by_cases hret : ret = -ENOSPC <;> simp_all


/-- The existing ring observer on this same original normal execution supplies
its actual appended physical journal and endpoint refinement. This is a local
supplied-history result, not initialized pipeline correspondence. -/
theorem consume_ring_normal {w v : World} (physical : RxRing.Inv epoch (PtrRing.init n) h w)
    (hr : (liftWG (consumeData msg src ds)).run w=.ok ((),v)) :
    let out := runPrefix (RxRing.consume msg src ds) w h
    out.1=.ok ((),v) ∧ (∃suffix,out.2=h++suffix) ∧
      RxRing.Safe (PtrRing.init n) out.2 ∧ RxRing.Inv epoch (PtrRing.init n) out.2 v := by
  have erasure := (RxRing.consume_erases msg src ds w h).trans hr
  obtain ⟨suffix,append,safe,post⟩ := RxRing.consume_preserves msg src ds w h physical
  rw [erasure] at post
  exact ⟨erasure,⟨suffix,append⟩,safe,post⟩

end Leanux.Proofs.WG.Queues.RxCredits
