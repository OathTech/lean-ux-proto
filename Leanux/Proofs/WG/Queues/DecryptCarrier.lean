import Leanux.Proofs.WG.Queues.RxIngressStable
import Leanux.Proofs.WG.Origins.OwnerDecrypt

/-! The original native decrypt preparation retains the supplied RX carriers.
Its publication reference remains a separate, source-acquired reservation until
the actual IRQ callback and peer payment. Normal endpoints do not assert totality. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DecryptCarrier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

def decryptView (w : WGWorld) := (carrierView w, stableView w)

theorem decryptView_store (h : wgStoreView v = wgStoreView w) :
    decryptView v = decryptView w := by
  have hd : v.dev = w.dev := congrArg WGStoreView.dev h
  unfold decryptView carrierView stableView keyView
  unfold peerView rxView RxCredits.keyWords RxCredits.currentCells RxRing.nativeCell
  rw [hd]

theorem invalidate_view (kid : KeypairId) : SameView decryptView (do
    let k ← getKeypair kid
    setKeypair kid {k with receiving := {k.receiving with isValid := false}}
    pure (none : Option RxPacket)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨k,read,mid,hread,hwrite⟩ := hr
  obtain ⟨readEq,ambientEq,d,hd,hk⟩ := KeyTimes.getKeypair_return kid w read k a mid hread
  subst read
  subst mid
  rw [MaterialOrigin.bind_ok_ambient] at hwrite
  obtain ⟨u,updated,upAmbient,hwrite,done⟩ := hwrite
  cases hwrite
  cases done
  let invalid : Keypair := {k with receiving := {k.receiving with isValid := false}}
  have words : RxCredits.keyWords {w with dev := some {d with keypairs := d.keypairs.insert kid invalid}} = RxCredits.keyWords w := by
    funext q
    by_cases same : kid = q
    · subst q; simp [RxCredits.keyWords,hd,hk,invalid]
    · simp [RxCredits.keyWords,hd,Std.TreeMap.getElem?_insert,same]
  change decryptView {w with dev := w.dev.map (fun d => {d with keypairs := d.keypairs.insert kid invalid})} = decryptView w
  simp only [hd,Option.map_some]
  unfold decryptView carrierView stableView keyView RxCredits.currentCells
  simp only [peerView,rxView,RxRing.nativeCell,hd,
    Option.map_some,Option.bind_some,words]

theorem decryptPacket_view (pkt : RxPacket) : SameView decryptView (decryptPacket pkt) := by
  intro initial
  let P := fun w => decryptView w = initial
  have get (kid : KeypairId) : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return kid w v k a b hr).1 ▸ hi
  have reject (k : Keypair) : Preserves P (KeyTimes.receiveReject k) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    exact (decryptView_store ((ProjectedAction.iff_run_ambient _ _ _).mp
      (decryptKeyReject_sameWGStore k) w a result v b hr)).trans hi
  change Preserves P _
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) P)
  intro noKey
  cases noKey with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (get pkt.keypair)
    intro key
    apply preserves_bind (reject key)
    intro rejected
    cases rejected with
    | true => exact (invalidate_view pkt.keypair).wp (fun x => x = initial)
    | false => exact ((Origins.receiveTail_sameWGWorld pkt key).factor decryptView).wp (fun x => x = initial)

theorem decryptPacket_state (pkt : RxPacket) (hi : CarrierState cs loans w)
    (a b : Ambient) (hr : ((decryptPacket pkt).run w).run a = .ok ((result,v),b)) :
    CarrierState cs loans v :=
  hi.view (congrArg Prod.fst ((ProjectedAction.iff_run_ambient _ _ _).mp
    (decryptPacket_view pkt) w a result v b hr))

theorem publicationMiddle_state (id : SkbId) (state : PacketState)
    (hi : CarrierState cs loans w) (a b : Ambient)
    (hr : ((publicationMiddle pid id state).run w).run a = .ok (((),v),b)) :
    CarrierState cs loans v := by
  have peer := (ProjectedAction.iff_run_ambient _ _ _).mp (publicationMiddle_frame pid id state) w a () v b hr
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp (publicationMiddle_shape pid id state) w a () v b hr
  have key := keyEffect_of_view (allowed := NoPromotion)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (publicationMiddle_keyView pid id state) w a () v b hr)
  exact ⟨inventory_shape hi.inventory shape,queueOwners_view hi.queues peer,
    protected_view hi.funded peer,rxCompatible_shape hi.keys.1 shape key,
    key.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩

theorem publish_factor (id : SkbId) (state : PacketState) :
    RxWorkers.publishSource id state = (do
      let pkt ← getRxSkb id
      let pid ← IndexOwner.peerDeref (.keypair pkt.keypair)
      peerGet pid
      publicationMiddle pid id state
      pure pid) := by
  simp only [RxWorkers.publishSource,publicationMiddle,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | intro x
    | (split <;> simp only [bind_assoc])

theorem publish_state (id : SkbId) (state : PacketState)
    (hi : CarrierState cs loans w) (a b : Ambient)
    (hr : ((RxWorkers.publishSource id state).run w).run a = .ok ((pid,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      CarrierState cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  rw [publish_factor] at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,read,ar,hread,owner,deref,ad,hderef,u,got,ag,hget,x,done,ab,hmid,hpure⟩ := hr
  cases u; cases x; cases hpure
  have readEq := (Packets.getRxSkb_current id w read pkt a ar hread).1
  subst read
  have derefEq := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun z => z=w)) w ar pid deref ad rfl hderef
  subst deref
  obtain ⟨d,p,hd,hp,pos,handoff⟩ := peerGet_handoff ad ag hget
  have loan : Loan w (some pid) got := by
    obtain ⟨dd,pp,hdd,hpp,hpos,effect⟩ := peerGet_loan pid w got ad ag hget
    refine ⟨dd,pp,hdd,hpp,hpos,?_,?_⟩
    · have dev := congrArg WGStoreView.dev effect
      change got.dev = some {dd with peers := dd.peers.insert pid {pp with refcount := pp.refcount + 1}} at dev
      simp only [peerView,creditWorld,dev,Option.map_some,Option.bind_some]
    · exact handoff.rx
  obtain ⟨dd,pp,hdd,hpp,hpos,funded⟩ := loan_protected loan hi.funded
  have eqd : dd=d := Option.some.inj (hdd.symm.trans hd)
  subst dd
  have eqp : pp=p := Option.some.inj (hpp.symm.trans hp)
  subst pp
  have key := keyEffect_of_view (allowed := NoPromotion)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_keyView pid) w ad () got ag hget)
  have acquired : CarrierState cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) got :=
    ⟨inventory_view hi.inventory handoff.rx,queueOwners_base hi.queues handoff.base,
      funded,key.rxCompatible handoff.rx hi.keys.1,
      key.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩
  exact ⟨d,p,hd,hp,pos,publicationMiddle_state id state acquired ag b hmid⟩

theorem ring_state (hi : CarrierState cs loans w) (ring : PtrRing SkbId) :
    CarrierState cs loans {w with dev := w.dev.map fun d => {d with decryptQueue := ring}} := by
  apply hi.view
  unfold carrierView peerView rxView keyView RxCredits.currentCells RxCredits.keyWords
  cases hd : w.dev <;> rfl

theorem payload_state {id : SkbId} {old out : RxPacket} (hi : CarrierState cs loans w)
    (hd : w.dev=some d) (hp : d.rxSkbs[id]?=some old)
    (peer : out.peer=old.peer) (key : out.keypair=old.keypair) :
    CarrierState cs loans (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) := by
  have shape : rxShape (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) = rxShape w := by
    unfold rxShape
    simp only [Packets.update,hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl ?_
    funext q
    by_cases eq : id=q
    · subst q; simp [hp,peer,key]
    · simp [Std.TreeMap.getElem?_insert,eq]
  have peers : peerView (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) = peerView w := by
    simp [peerView,Packets.update,hd]
  have keys : keyView (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) = keyView w := by
    unfold keyView RxCredits.keyWords RxCredits.currentCells
    simp [Packets.update,hd]
  have effect := keyEffect_of_view (allowed:=NoPromotion) keys
  exact ⟨inventory_shape hi.inventory shape,queueOwners_view hi.queues peers,
    protected_view hi.funded peers,rxCompatible_shape hi.keys.1 shape effect,
    effect.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩

theorem set_payload_state {id : SkbId} {old out : RxPacket} (hi : CarrierState cs loans w)
    (hd : w.dev=some d) (hp : d.rxSkbs[id]?=some old)
    (peer : out.peer=old.peer) (key : out.keypair=old.keypair)
    (a b : Ambient) (hr : ((setRxSkb id (fun _ => out)).run w).run a=.ok (((),v),b)) :
    CarrierState cs loans v := by
  rw [Packets.setRxSkb_run w a d id old (fun _ => out) hd hp] at hr
  cases hr
  exact payload_state hi hd hp peer key

theorem readDecrypt_state (id : SkbId) (hi : CarrierState cs loans w) (a b : Ambient)
    (hr : ((RxOrigin.readDecrypt id).run w).run a=.ok (((pkt,result),v),b)) :
    CarrierState cs loans v ∧ (∃ d, v.dev=some d ∧ d.rxSkbs[id]?=some pkt) ∧
      ∀ out, result=some out → out.peer=pkt.peer ∧ out.keypair=pkt.keypair := by
  unfold RxOrigin.readDecrypt at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨old,read,ar,hread,decrypted,done,ad,hdecrypt,hpure⟩ := hr
  cases hpure
  have readEq := (Packets.getRxSkb_current id w read pkt a ar hread).1
  subst read
  obtain ⟨_,d,hd,hp⟩ := (Packets.getRxSkb_current id w w pkt a ar hread).2
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (decryptPacket_view pkt) w ar result v b hdecrypt
  have stored : (v.dev.bind fun d => d.rxSkbs[id]?)=some pkt := by
    have cell := congrFun (congrArg (fun x => x.1.2.1.2) frame) id
    simpa [decryptView,carrierView,rxView,hd,hp] using cell
  obtain ⟨dev,hdev,hpacket⟩ := Option.bind_eq_some_iff.mp stored
  refine ⟨hi.view (congrArg Prod.fst frame),⟨dev,hdev,hpacket⟩,?_⟩
  intro out hout
  obtain ⟨_,_,_,_,fields⟩ := Affiliation.decryptPacket_fields pkt out w v ar b (hout ▸ hdecrypt)
  exact ⟨fields.1,fields.2.1⟩

def Prepared (cs : Ledger) (loans : Reservations) (result : Option PeerId) (w : WGWorld) : Prop :=
  match result with
  | none => CarrierState cs loans w
  | some pid => ∃ o : Owner, o.slot=pid ∧ CarrierState cs (o::loans) w

theorem getDev_current (a b : Ambient)
    (hr : ((getDev).run w).run a=.ok ((d,v),b)) : v=w ∧ b=a ∧ w.dev=some d := by
  cases hd : w.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some dev =>
    have eq : (dev=d ∧ w=v) ∧ a=b := by simpa [getDev,hd] using hr
    rcases eq with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨rfl,rfl,rfl⟩

theorem prepare_factor : RxWorkers.prepareSource = (do
    let d ← getDev
    match d.decryptQueue.consume with
    | (none, _) => do
      _ ← branch .decWorkerConsumed false
      pure none
    | (some id, ring) => do
      _ ← branch .decWorkerConsumed true
      modifyDev fun d => {d with decryptQueue := ring}
      let (_,decrypted) ← RxOrigin.readDecrypt id
      if ← branch .decWorkerDecrypted decrypted.isSome then
        let some out := decrypted | invariant "unreachable"
        setRxSkb id fun _ => out
        return some (← RxWorkers.publishSource id .crypted)
      else return some (← RxWorkers.publishSource id .dead)) := by
  simp only [RxWorkers.prepareSource,RxOrigin.readDecrypt,bind_assoc,pure_bind]
  rfl

theorem prepare_state (hi : CarrierState cs loans w) (a b : Ambient)
    (hr : ((RxWorkers.prepareSource).run w).run a=.ok ((result,v),b)) :
    Prepared cs loans result v := by
  rw [prepare_factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨d,read,ar,hget,tail⟩ := hr
  obtain ⟨readEq,ambientEq,hd⟩ := getDev_current a ar hget
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
      exact hi
    | some id =>
      simp only [hc,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨value,after,aa,hbranch,u,ringWorld,ab,hring,pair,readWorld,ac,hread,decision,decWorld,ad,hdecision,tail⟩ := tail
      change Except.ok ((true,w),CounterWindow.record a .decWorkerConsumed true)=Except.ok ((value,after),aa) at hbranch
      cases hbranch
      cases hring
      rcases pair with ⟨pkt,decrypted⟩
      have hiRing := ring_state hi ring
      obtain ⟨hiRead,⟨dev,hdev,hpkt⟩,fields⟩ := readDecrypt_state id hiRing _ ac hread
      change Except.ok ((decrypted.isSome,readWorld),CounterWindow.record ac .decWorkerDecrypted decrypted.isSome)=
        Except.ok ((decision,decWorld),ad) at hdecision
      cases hdecision
      cases decrypted with
      | none =>
        simp only [Option.isSome_none,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨pid,final,af,hpublish,hpure⟩ := tail
        cases hpure
        obtain ⟨d,p,_,_,_,state⟩ := publish_state id .dead hiRead _ b hpublish
        exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,state⟩
      | some out =>
        simp only [Option.isSome_some,ite_true,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨u,updated,au,hwrite,pid,final,af,hpublish,hpure⟩ := tail
        cases u
        cases hpure
        have hiWrite := set_payload_state hiRead hdev hpkt (fields out rfl).1 (fields out rfl).2 _ au hwrite
        obtain ⟨d,p,_,_,_,state⟩ := publish_state id .crypted hiWrite _ b hpublish
        exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,state⟩

end Leanux.Proofs.WG.Queues.RxCredits.DecryptCarrier
