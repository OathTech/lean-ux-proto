import Leanux.Proofs.WG.Origins.OwnerIngress
import Leanux.Proofs.WG.Origins.OwnerCreation
import Leanux.Proofs.WG.Queues.RxIngressCarrier

/-! Normal admission repayment and the actual postallocation enqueue/cleanup
preserve the receiving-owner carrier. The allocation premise is used only at
the allocation cut; no positive reference count or totality is assumed. -/
namespace Leanux.Proofs.WG.OwnerConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

private theorem carrier_transport (hi : OwnerBounds.Carrier w)
    (material : Origins.Retains w v) (geometry : allocationMetadata v = allocationMetadata w)
    (shape : rxShape v = rxShape w) (keys : KeyEffect NoPromotion w v) :
    OwnerBounds.Carrier v := by
  constructor
  · apply owners_retain hi.owners material
    intro before after hb ha _
    obtain ⟨d, hd, fields⟩ := allocationMetadata_device geometry ha
    have same : d = before := Option.some.inj (hd.symm.trans hb)
    subst d
    exact Nat.le_of_eq (congrArg DeviceAllocationMetadata.nextPeer fields).symm
  · exact rxCompatible_shape hi.compatible shape keys
  · intro after ha id pkt hp
    obtain ⟨before, hb, fields⟩ := allocationMetadata_device geometry ha
    have old : ((w.dev.bind fun d => d.rxSkbs[id]?).map fun p => (p.peer,p.keypair)) =
        some (pkt.peer,pkt.keypair) := by
      simpa [rxShape,ha,hp] using (congrFun (congrArg Prod.snd shape) id).symm
    obtain ⟨oldPacket, hold, same⟩ := Option.map_eq_some_iff.mp old
    have resident : before.rxSkbs[id]? = some oldPacket := by simpa [hb] using hold
    have frontier : after.nextKeypairId = before.nextKeypairId :=
      congrArg DeviceAllocationMetadata.nextKeypair fields
    have word : oldPacket.keypair = pkt.keypair := congrArg Prod.snd same
    rw [frontier, ← word]
    exact hi.rxKeys before hb id oldPacket resident

theorem peerPut_preserves (pid : Option PeerId) :
    Preserves OwnerBounds.Carrier (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.peerPut_material pid) w a result v b hr
  apply carrier_transport hi _
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_metadata pid) w a result v b hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (rxShape_peerPut pid) w a result v b hr)
    ((KeyEffects.iff_run_ambient _ _).mp (peerPut_keyEffect (allowed := NoPromotion) pid)
      w a result v b hr)
  unfold Origins.Retains
  rw [material]
  exact Origins.RetainsView.refl _

private theorem carrier_sameDev (hi : OwnerBounds.Carrier w) (hd : v.dev = w.dev) :
    OwnerBounds.Carrier v := by
  exact ⟨by simpa only [CurrentIdentity.ReceivingOwnersBelow, hd] using hi.owners,
    by simpa only [RxCompatible,KeyCompatible,hd] using hi.compatible,
    by simpa only [RxKeysBelow,hd] using hi.rxKeys⟩

private theorem carrier_map (f : Device → Device)
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (hi : OwnerBounds.Carrier w) :
    OwnerBounds.Carrier {w with dev := w.dev.map f} := by
  constructor
  · intro d hd id k hk valid pid word
    obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [peer]
    exact hi.owners old ho id k (by simpa only [keys] using hk) valid pid word
  · intro d id pkt hd hp other key ho hk
    obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hd
    have same : other = f old := Option.some.inj (ho.symm.trans (by simp [hold]))
    subst other
    exact hi.compatible old id pkt hold (by simpa only [rx] using hp) old key hold
      (by simpa only [keys] using hk)
  · intro d hd id pkt hp
    obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hd
    rw [frontier]
    exact hi.rxKeys old ho id pkt (by simpa only [rx] using hp)

private theorem packetState_preserves (id : SkbId) (state : PacketState) :
    Preserves OwnerBounds.Carrier (setRxSkb id fun p => {p with state}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hd : w.dev with
  | none => simp [setRxSkb, liftSkb_run, hd] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,hd,hp,
        invariant,AmbientM.invariant] at hr
      cases hr
    | some pkt =>
      rw [Packets.setRxSkb_run w a d id pkt (fun p => {p with state}) hd hp] at hr
      cases hr
      have device : (Packets.update w (fun d => {d with rxSkbs := d.rxSkbs.insert id {pkt with state}})).dev =
          some {d with rxSkbs := d.rxSkbs.insert id {pkt with state}} := by simp [Packets.update,hd]
      constructor
      · intro out ho kid key hk valid pid word
        have same := Option.some.inj (ho.symm.trans device)
        subst out
        exact hi.owners d hd kid key hk valid pid word
      · intro out slot packet ho hpacket other key ho' hk
        have same := Option.some.inj (ho.symm.trans device)
        have same' := Option.some.inj (ho'.symm.trans device)
        subst out
        subst other
        by_cases same : id = slot
        · subst slot
          have eq : packet = {pkt with state} := by simpa using hpacket.symm
          subst packet
          exact hi.compatible d id pkt hd hp d key hd hk
        · exact hi.compatible d slot packet hd
            (by simpa [Std.TreeMap.getElem?_insert,same] using hpacket) d key hd hk
      · intro out ho slot packet hpacket
        have same := Option.some.inj (ho.symm.trans device)
        subst out
        by_cases same : id = slot
        · subst slot
          have eq : packet = {pkt with state} := by simpa using hpacket.symm
          subst packet
          exact hi.rxKeys d hd id pkt hp
        · exact hi.rxKeys d hd slot packet
            (by simpa [Std.TreeMap.getElem?_insert,same] using hpacket)

theorem freeRxSkb_preserves (id : SkbId) :
    Preserves OwnerBounds.Carrier (freeRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hd : w.dev with
  | none => simp [freeRxSkb,liftSkb_run,hd] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,hd,hp,
        invariant,AmbientM.invariant] at hr
      cases hr
    | some pkt =>
      rw [Packets.freeRxSkb_run w a d id pkt hd hp] at hr
      cases hr
      have device : (Packets.update w (fun d => {d with rxSkbs := d.rxSkbs.erase id})).dev =
          some {d with rxSkbs := d.rxSkbs.erase id} := by simp [Packets.update,hd]
      have surviving (slot : SkbId) (packet : RxPacket)
          (h : (d.rxSkbs.erase id)[slot]? = some packet) : d.rxSkbs[slot]? = some packet := by
        by_cases same : id = slot
        · subst slot; simp at h
        · simpa [Std.TreeMap.getElem?_erase,same] using h
      constructor
      · intro out ho kid key hk valid pid word
        have same := Option.some.inj (ho.symm.trans device)
        subst out
        exact hi.owners d hd kid key hk valid pid word
      · intro out slot packet ho hpacket other key ho' hk
        have same := Option.some.inj (ho.symm.trans device)
        have same' := Option.some.inj (ho'.symm.trans device)
        subst out
        subst other
        exact hi.compatible d slot packet hd (surviving slot packet hpacket) d key hd hk
      · intro out ho slot packet hpacket
        have same := Option.some.inj (ho.symm.trans device)
        subst out
        exact hi.rxKeys d hd slot packet (surviving slot packet hpacket)

theorem enqueuePerDeviceAndPeerRx_preserves (id : SkbId) :
    Preserves OwnerBounds.Carrier (enqueuePerDeviceAndPeerRx id) := by
  have readRx (slot : SkbId) : Preserves OwnerBounds.Carrier (getRxSkb slot) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a pkt v b hi hr
    exact (Packets.getRxSkb_current slot w v pkt a b hr).1 ▸ hi
  have readPeer (pid : PeerId) : Preserves OwnerBounds.Carrier (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    exact (Queues.getPeer_normal pid w v p a b hr).1 ▸ hi
  have store {α : Type} (a : WG.M α) (h : SameWGStore a) : Preserves OwnerBounds.Carrier a := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v finalAmbient hi hr
    exact carrier_sameDev hi (congrArg WGStoreView.dev
      ((ProjectedAction.iff_run_ambient _ _ _).mp h w ambient result v finalAmbient hr))
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (allocation_release_head setRxSkb; exact packetState_preserves _ _)
    | (allocation_release_head getRxSkb; exact readRx _)
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head getDev; exact store _ getDev_sameWGStore)
    | (allocation_release_head cpumaskNextOnlineFrom; exact store _ (cpumaskNextOnlineFrom_sameStore _))
    | (allocation_release_head setPeer; unfold setPeer)
    | (allocation_release_head modifyDev
       unfold modifyDev
       apply hoare_modify
       intro w hi
       exact carrier_map _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ OwnerBounds.Carrier)
    | allocation_release_step

private theorem publication_metadata (id : SkbId) (state : PacketState) :
    SameView allocationMetadata (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  intro initial
  let P := fun w => allocationMetadata w = initial
  have readRx (slot : SkbId) : Preserves P (getRxSkb slot) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a pkt v b hi hr
    exact (Packets.getRxSkb_current slot w v pkt a b hr).1 ▸ hi
  have readPeer (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    exact (Queues.getPeer_normal pid w v p a b hr).1 ▸ hi
  change Preserves P _
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [invariant,monadLift_self]
  repeat' first
    | (allocation_release_head getRxSkb; exact readRx _)
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head peerGet; exact (peerGet_metadata _).wp (fun s => s = initial))
    | (allocation_release_head setPeer; exact (setPeer_metadata _ _).wp (fun s => s = initial))
    | (allocation_release_head setRxSkb; exact (setRxSkb_metadata _ _).wp (fun s => s = initial))
    | (allocation_release_head peerPut; exact (peerPut_metadata _).wp (fun s => s = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | allocation_release_step

theorem enqueuePerPeerRx_preserves (id : SkbId) (state : PacketState) :
    Preserves OwnerBounds.Carrier (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  obtain ⟨_, shape, keys⟩ := publication_preservation id state a b hr
  exact carrier_transport hi
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.Retaining.enqueuePerPeerRx_material_native (pure ())
        (Origins.Retaining.of_view (SameView.pure Origins.view ())) id state) w a () v b hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (publication_metadata id state) w a () v b hr)
    shape keys

/-- No-key and dead-peer normal returns repay the source references. A failed
lookup, record, getter or payment remains a Stop and supplies no endpoint. -/
theorem admitted_none (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (w v : WGWorld) (ambient finalAmbient : Ambient) (hi : OwnerBounds.Carrier w)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient =
      .ok ((none,v),finalAmbient)) : OwnerBounds.Carrier v := by
  rw [RxOrigin.admitSource_factor] at hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨entry,a,aa,lookup,acquired,b,ab,key,noKey,c,ac,decision,rest⟩ := hr
  rcases acquired with ⟨kp,pid⟩
  have ha := (hoare_iff_run_ambient _ _ _).mp
    (OwnerIndex.indexLookup_preserves [.keypair] (u32le msg 4)) w ambient entry a aa hi lookup
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (OwnerIngress.receiveKey_preserves entry) a aa (kp,pid) b ab ha key
  have hc := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair kp.isNone) OwnerBounds.Carrier)
    b ab noKey c ac hb decision
  cases noKey with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,z,az,pay,done⟩ := rest
    cases u
    obtain ⟨⟨_,rfl⟩,rfl⟩ := done
    exact (hoare_iff_run_ambient _ _ _).mp (peerPut_preserves pid) c ac () v finalAmbient hc pay
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
        simp only [MaterialOrigin.bind_ok_ambient] at rest
        obtain ⟨peer,d,ad,read,dead,e,ae,decision,rest⟩ := rest
        have hd : OwnerBounds.Carrier d := (Queues.getPeer_normal pid c d peer ac ad read).1 ▸ hc
        have he := (hoare_iff_run_ambient _ _ _).mp
          (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) OwnerBounds.Carrier)
          d ad dead e ae hd decision
        cases dead with
        | true =>
          simp only [ite_true,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨u,f,af,key,u',g,ag,pay,done⟩ := rest
          cases u
          cases u'
          obtain ⟨⟨_,rfl⟩,rfl⟩ := done
          have hf := (hoare_iff_run_ambient _ _ _).mp
            (OwnerCreation.keypairPut_preserves (some kid) false) e ae () f af he key
          exact (hoare_iff_run_ambient _ _ _).mp
            (peerPut_preserves (some pid)) f af () v finalAmbient hf pay
        | false =>
          simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at rest
          obtain ⟨slot,z,az,allocate,bad⟩ := rest
          simp at bad

theorem admitSource_spec (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List LifetimeEvent) :
    Hoare (RxOrigin.admitSource msg src ds)
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result with
  | none => exact admitted_none msg src ds w v a b hi.2 hr
  | some ctx => exact OwnerIngress.admitted_carrier msg src ds ctx w v a b hi.2 hi.1 hr

/-- The exact source suffix includes queue acceptance, EPIPE publication and
the ENOSPC payment/free branch, retaining every recorded decision and Stop. -/
theorem finishSource_preserves (ctx : RxOrigin.Admission) :
    Preserves OwnerBounds.Carrier (finishSource ctx) := by
  unfold finishSource RxOrigin.finishWith
  simp (config := {zeta := false}) only [branch,WG.orM,monadLift_self]
  repeat' first
    | (allocation_release_head enqueuePerDeviceAndPeerRx; exact enqueuePerDeviceAndPeerRx_preserves _)
    | (allocation_release_head enqueuePerPeerRx; exact enqueuePerPeerRx_preserves _ _)
    | (allocation_release_head keypairPut; exact OwnerCreation.keypairPut_preserves _ _)
    | (allocation_release_head peerPut; exact peerPut_preserves _)
    | (allocation_release_head freeRxSkb; exact freeRxSkb_preserves _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ OwnerBounds.Carrier)
    | allocation_release_step

/-- The original concrete consume call preserves the carrier from its actual
input allocation invariant. This is a partial normal-return contract. -/
theorem consumeData_spec (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List LifetimeEvent) :
    Hoare (consumeData msg src ds)
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w) := by
  rw [← RxOrigin.consumeSource_eq]
  unfold RxOrigin.consumeSource RxOrigin.consumeWith
  apply hoare_bind _ _ (admitSource_spec msg src ds history)
  intro result
  cases result with
  | none => exact preserves_pure ()
  | some ctx => exact finishSource_preserves ctx

end Leanux.Proofs.WG.OwnerConsume
