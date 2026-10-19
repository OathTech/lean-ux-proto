import Leanux.Proofs.WG.Origins.OwnerIndex
import Leanux.Proofs.WG.Packets.RxOriginCuts

/-! The actual RX allocation/admission cut combines the owner carrier with the
existing allocation observer. Resident-key slot bounds come from AllocationInv;
they are not inferred from nullable compatibility or current-key validity. -/
namespace Leanux.Proofs.WG.OwnerIngress
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

private theorem carrier_frame (hi : Carrier w) (material : Origins.Retains w v)
    (fields : Affiliation.view v = Affiliation.view w) (packets : rxView v = rxView w) :
    Carrier v := by
  have frontiers (before after : Device) (hb : w.dev = some before) (ha : v.dev = some after) :
      after.nextPeer = before.nextPeer ∧ after.nextKeypairId = before.nextKeypairId := by
    have eq : Affiliation.state after = Affiliation.state before :=
      Option.some.inj (by simpa only [Affiliation.view, hb, ha, Option.map_some] using fields)
    exact ⟨congrArg Affiliation.State.nextPeer eq, congrArg Affiliation.State.nextKey eq⟩
  constructor
  · apply owners_retain hi.owners material
    intro before after hb ha _
    exact Nat.le_of_eq (frontiers before after hb ha).1.symm
  · exact (keyEffect_of_view (allowed := NoPromotion) (keyView_affiliation fields)).rxCompatible
      packets hi.compatible
  · intro after ha id pkt hp
    have oldRx : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
      simpa [rxView, ha, hp] using (congrFun (congrArg Prod.snd packets) id).symm
    obtain ⟨before, hb, oldPacket⟩ := Option.bind_eq_some_iff.mp oldRx
    rw [(frontiers before after hb ha).2]
    exact hi.rxKeys before hb id pkt oldPacket

theorem receiveKey_preserves (entry : Option (IndexOwner × PeerId)) :
    Preserves Carrier (Affiliation.receiveKeyAcquire entry) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have fields := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.receiveKeyAcquire_spec entry (Affiliation.view w))
    w ambient result v finalAmbient rfl hr).1
  have packets := congrArg Prod.snd ((ProjectedAction.iff_run_ambient _ _ _).mp
    (receiveKey_credit_frame entry) w ambient result v finalAmbient hr)
  apply carrier_frame hi _ fields packets
  cases entry with
  | none =>
    simp [Affiliation.receiveKeyAcquire, keypairGetNull, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact Origins.Retains.refl _
  | some entry =>
    rcases entry with ⟨owner, pid⟩
    cases owner with
    | handshake id =>
      simp [Affiliation.receiveKeyAcquire, invariant, AmbientM.invariant] at hr
      cases hr
    | keypair id =>
      simp only [Affiliation.receiveKeyAcquire, pure_bind, MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨kp, after, middle, get, tail⟩ := hr
      cases tail
      exact (ProjectedAction.iff_run_ambient _ _ _).mp
        (Origins.Retaining.keypairGet_material (some id)) w ambient kp v finalAmbient get

/-- The source allocation keeps all old references. The new packet's key is
resident with its exact owner word, and the existing R2 endpoint supplies its
slot bound. This does not assume a total allocation or an initialized state. -/
theorem allocation_carrier (pkt : RxPacket) (w v : WGWorld) (slot : SkbId)
    (ambient finalAmbient : Ambient) (hi : Carrier w)
    (allocation : AllocationInv history v) (word : KeyWord pkt.keypair pkt.peer v)
    (hr : ((newRxSkb pkt).run w).run ambient = .ok ((slot, v), finalAmbient)) : Carrier v := by
  obtain ⟨d, hd, rfl, hv, _, _⟩ :=
    RxOrigin.allocation_record pkt ⟨slot, w, v, ambient, finalAmbient⟩ hr
  dsimp only at hd hv
  have device : v.dev = some {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1} := by
    simpa only [Packets.update, hd, Option.map_some] using congrArg WGWorld.dev hv
  let allocated := {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}
  have selected : KeyCompatible pkt.peer pkt.keypair v := by
    obtain ⟨before, key, hb, hk, owner⟩ := word
    intro after other ha ho
    have same : after = before := Option.some.inj (ha.symm.trans hb)
    subst after
    have same : other = key := Option.some.inj (ho.symm.trans hk)
    subst other
    exact Or.inr owner
  have below : pkt.keypair < d.nextKeypairId := by
    obtain ⟨before, key, hb, hk, _⟩ := word
    have same : before = allocated := Option.some.inj (hb.symm.trans device)
    subst before
    exact allocation.keySlots allocated device pkt.keypair key hk
  constructor
  · intro after ha kid key hk valid pid owner
    have same : after = allocated := Option.some.inj (ha.symm.trans device)
    subst after
    exact hi.owners d hd kid key hk valid pid owner
  · intro after id packet ha hp other key ho hk
    have same : after = allocated := Option.some.inj (ha.symm.trans device)
    have same' : other = after := Option.some.inj (ho.symm.trans ha)
    subst other
    subst after
    by_cases atSlot : d.nextSkb = id
    · subst id
      have same : packet = pkt := by simpa only [allocated, Std.TreeMap.getElem?_insert_self,
        Option.some.injEq] using hp.symm
      subst packet
      exact selected allocated key device hk
    · have old : d.rxSkbs[id]? = some packet := by
        simpa [allocated, Std.TreeMap.getElem?_insert, atSlot] using hp
      exact hi.compatible d id packet hd old d key hd hk
  · intro after ha id packet hp
    have same : after = allocated := Option.some.inj (ha.symm.trans device)
    subst after
    by_cases atSlot : d.nextSkb = id
    · subst id
      have same : packet = pkt := by simpa only [allocated, Std.TreeMap.getElem?_insert_self,
        Option.some.injEq] using hp.symm
      subst packet
      exact below
    · have old : d.rxSkbs[id]? = some packet := by
        simpa [allocated, Std.TreeMap.getElem?_insert, atSlot] using hp
      exact hi.rxKeys d hd id packet old

/-- Erasure of the already-existing admission allocation observer. -/
theorem admitPrefix_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (RxOrigin.admitPrefix msg src ds) (RxOrigin.admitSource msg src ds) := by
  have fresh (pkt : RxPacket) : ErasesStatePrefix (newRxSkbPrefix pkt) (newRxSkb pkt) :=
    PacketAllocation.erases (.rx pkt)
  unfold RxOrigin.admitPrefix RxOrigin.admitSource RxOrigin.admitWith
  repeat' first
    | with_reducible exact indexLookupPrefix_erases _ _
    | with_reducible exact keypairGetPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact keypairPutPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact fresh _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

/-- Successful admission preserves the carrier using the same input allocation
history and exact original source receipt. Normal None and postallocation
queue/cleanup calls are separate propagation obligations. -/
theorem admitted_carrier (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (ctx : RxOrigin.Admission) (w v : WGWorld) (ambient finalAmbient : Ambient)
    (hi : Carrier w) (allocation : AllocationInv history w)
    (hr : ((RxOrigin.admitSource msg src ds).run w).run ambient =
      .ok ((some ctx, v), finalAmbient)) : Carrier v := by
  obtain ⟨entry, a, aa, b, ab, c, ac, peer, d, ad, e, ae, lookup, key, noKey,
    read, dead, _, allocate⟩ := RxOrigin.admission_execution msg src ds ctx w v ambient finalAmbient hr
  have ha := (hoare_iff_run_ambient _ _ _).mp
    (OwnerIndex.indexLookup_preserves [.keypair] (u32le msg 4)) w ambient entry a aa hi lookup
  have hb := (hoare_iff_run_ambient _ _ _).mp (receiveKey_preserves entry)
    a aa (some ctx.packet.keypair, some ctx.packet.peer) b ab ha key
  have hc : c = b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair false) (fun g => g = b))
    b ab false c ac rfl noKey
  have hd : d = c := (Queues.getPeer_normal ctx.packet.peer c d peer ac ad read).1
  have he : e = d := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g = d))
    d ad false e ae rfl dead
  have before : Carrier e := by simpa only [he, hd, hc] using hb
  have observed := (admitPrefix_erases msg src ds w ambient history).trans hr
  have after := (RxOrigin.admit_allocation msg src ds w ambient history allocation).choose_spec.2.2
  rw [observed] at after
  exact allocation_carrier ctx.packet e v ctx.slot ae finalAmbient before after
    (admitted_key_word ambient finalAmbient hr) allocate

end Leanux.Proofs.WG.OwnerIngress
