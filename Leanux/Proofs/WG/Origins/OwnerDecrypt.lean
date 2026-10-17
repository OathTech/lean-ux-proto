import Leanux.Proofs.WG.Origins.OwnerConsume
import Leanux.Proofs.WG.Origins.OwnerChecks
import Leanux.Proofs.WG.Origins.CurrentRx

/-! The actual decrypt call preserves receiving-owner bounds, nullable packet
compatibility and RX key-slot bounds. Rejection may invalidate a key; no
successful authentication, positive reference count or totality is assumed. -/
namespace Leanux.Proofs.WG.OwnerDecrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

private theorem invalidate_preserves (kid : KeypairId) :
    Preserves OwnerBounds.Carrier (do
      let key ← getKeypair kid
      setKeypair kid {key with receiving := {key.receiving with isValid := false}}
      pure (none : Option RxPacket)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  simp only [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨key,read,readAmbient,hread,u,after,afterAmbient,hwrite,done⟩ := hr
  obtain ⟨readEq,ambientEq,d,hd,hkey⟩ := KeyTimes.getKeypair_return kid w read key a readAmbient hread
  subst read
  subst readAmbient
  cases hwrite
  cases done
  let invalid := {key with receiving := {key.receiving with isValid := false}}
  have device : ({w with dev := w.dev.map fun d => {d with keypairs := d.keypairs.insert kid invalid}} : WGWorld).dev =
      some {d with keypairs := d.keypairs.insert kid invalid} := by simp [hd]
  constructor
  · intro out ho slot k hk valid pid word
    have eq := Option.some.inj (ho.symm.trans device)
    subst out
    by_cases chosen : kid = slot
    · subst slot
      have eq : k = invalid := by simpa using hk.symm
      subst k
      cases valid
    · exact hi.owners d hd slot k (by simpa [Std.TreeMap.getElem?_insert,chosen] using hk)
        valid pid word
  · intro out id pkt ho hp other k ho' hk
    have eq := Option.some.inj (ho.symm.trans device)
    have eq' := Option.some.inj (ho'.symm.trans device)
    subst out
    subst other
    by_cases chosen : kid = pkt.keypair
    · have eq : k = invalid := by simpa [chosen] using hk.symm
      subst k
      exact hi.compatible d id pkt hd hp d key hd (chosen ▸ hkey)
    · exact hi.compatible d id pkt hd hp d k hd
        (by simpa [Std.TreeMap.getElem?_insert,chosen] using hk)
  · intro out ho id pkt hp
    have eq := Option.some.inj (ho.symm.trans device)
    subst out
    exact hi.rxKeys d hd id pkt hp

theorem decryptPacket_preserves (pkt : RxPacket) :
    Preserves OwnerBounds.Carrier (decryptPacket pkt) := by
  have read (kid : KeypairId) : Preserves OwnerBounds.Carrier (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi hr
    exact (KeyTimes.getKeypair_return kid w v key a b hr).1 ▸ hi
  have reject (key : Keypair) : Preserves OwnerBounds.Carrier (KeyTimes.receiveReject key) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
      (decryptKeyReject_sameWGStore key) w a result v b hr
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi (congrArg WGStoreView.dev frame)
  have tail (key : Keypair) : Preserves OwnerBounds.Carrier (KeyTimes.receiveTail pkt key) := by
    unfold KeyTimes.receiveTail WG.orM
    simp (config := {zeta := false}) only [branch,hiddenAlloc,invariant]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ OwnerBounds.Carrier)
      | allocation_release_step
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) OwnerBounds.Carrier)
  intro noKey
  cases noKey with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (read pkt.keypair)
    intro key
    apply preserves_bind (reject key)
    intro rejected
    cases rejected with
    | true => exact invalidate_preserves pkt.keypair
    | false => exact tail key

theorem readDecrypt_preserves (id : SkbId) :
    Preserves OwnerBounds.Carrier (RxOrigin.readDecrypt id) := by
  have read : Preserves OwnerBounds.Carrier (getRxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a pkt v b hi hr
    exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi
  unfold RxOrigin.readDecrypt
  exact preserves_bind read fun pkt =>
    preserves_bind (decryptPacket_preserves pkt) (fun _ => preserves_pure _)

/-- This discharges both explicit native obligations of the existing owner
decrypt observer. Its captured entry and strict earlier session prefix are
unchanged, including the safe journal retained on a Stop. -/
theorem decrypt (id : SkbId) : OwnerChecks.Preserves (Origins.HistoryAdapters.decrypt id) :=
  OwnerChecks.decrypt id
    (CurrentChecks.decrypt id (CurrentRx.readDecrypt_preserves id)) (readDecrypt_preserves id)

/-- The publication prefix acquires its actual peer reference and retains the
carrier before IRQ callbacks and the later payment. -/
theorem publishSource_preserves (id : SkbId) (state : PacketState) :
    Preserves OwnerBounds.Carrier (Queues.RxWorkers.publishSource id state) := by
  have readRx (slot : SkbId) : Preserves OwnerBounds.Carrier (getRxSkb slot) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a pkt v b hi hr
    exact (Packets.getRxSkb_current slot w v pkt a b hr).1 ▸ hi
  have readPeer (pid : PeerId) : Preserves OwnerBounds.Carrier (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    exact (Queues.getPeer_normal pid w v p a b hr).1 ▸ hi
  have acquire (pid : PeerId) : Preserves OwnerBounds.Carrier (peerGet pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    have material := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.Retaining.peerGet_material pid) w a result v b hr
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_transport)
      hi _ ((ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_metadata pid) w a result v b hr)
      ((ProjectedAction.iff_run_ambient _ _ _).mp (rxShape_peerGet pid) w a result v b hr)
      (keyEffect_of_view ((ProjectedAction.iff_run_ambient _ _ _).mp
        (peerGet_keyView pid) w a result v b hr))
    unfold Origins.Retains
    rw [material]
    exact Origins.RetainsView.refl _
  unfold Queues.RxWorkers.publishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (allocation_release_head getRxSkb; exact readRx _)
    | (allocation_release_head IndexOwner.peerDeref
       exact indexOwner_peerDeref_preserves _ OwnerBounds.Carrier)
    | (allocation_release_head peerGet; exact acquire _)
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head setRxSkb
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.packetState_preserves) _ _)
    | (allocation_release_head setPeer
       unfold setPeer modifyDev
       apply hoare_modify
       intro w hi
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_map)
         _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ OwnerBounds.Carrier)
    | allocation_release_step

private theorem decryptPacket_rx (pkt : RxPacket) : SameView rxView (decryptPacket pkt) := by
  intro initial
  let P := fun w => rxView w = initial
  have read (kid : KeypairId) : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi hr
    exact (KeyTimes.getKeypair_return kid w v key a b hr).1 ▸ hi
  have write (kid : KeypairId) (key : Keypair) : Preserves P (setKeypair kid key) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    simpa [P,rxView,Option.bind_map,Function.comp_def] using hi
  change Preserves P _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (allocation_release_head getKeypair; exact read _)
    | (allocation_release_head setKeypair; exact write _ _)
    | (allocation_release_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp P)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | allocation_release_step

/-- The source getter is still resident after decrypt, and every normal
plaintext result has the same two affiliation fields as that stored packet. -/
private theorem readDecrypt_spec (id : SkbId) :
    Hoare (RxOrigin.readDecrypt id) OwnerBounds.Carrier (fun result w =>
      OwnerBounds.Carrier w ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[id]? = some result.1 ∧
        ∀ out, result.2 = some out → out.peer = result.1.peer ∧ out.keypair = result.1.keypair) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  simp only [RxOrigin.readDecrypt,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,read,readAmbient,hread,decrypted,after,afterAmbient,run,done⟩ := hr
  obtain ⟨readEq,ambientEq,d,hd,hpkt⟩ := Packets.getRxSkb_current id w read pkt a readAmbient hread
  subst read
  subst readAmbient
  cases done
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (decryptPacket_rx pkt) w a decrypted v b run
  have stored : (v.dev.bind fun d => d.rxSkbs[id]?) = some pkt := by
    simpa [rxView,hd,hpkt] using congrFun (congrArg Prod.snd frame) id
  obtain ⟨outDev,outDevice,outPacket⟩ := Option.bind_eq_some_iff.mp stored
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (decryptPacket_preserves pkt)
    w a decrypted v b hi run,outDev,outDevice,outPacket,?_⟩
  intro out value
  change decrypted = some out at value
  subst decrypted
  have fields := RxOrigin.decryptPacket_record pkt out w v a b run
  exact ⟨by simpa only using congrArg RxPacket.peer fields,
    by simpa only using congrArg RxPacket.keypair fields⟩

private theorem replacePacket_spec (id : SkbId) (pkt out : RxPacket)
    (peer : out.peer = pkt.peer) (key : out.keypair = pkt.keypair) :
    Hoare (setRxSkb id fun _ => out)
      (fun w => OwnerBounds.Carrier w ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[id]? = some pkt)
      (fun _ w => OwnerBounds.Carrier w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  obtain ⟨d,hd,hpkt⟩ := hi.2
  rw [Packets.setRxSkb_run w a d id pkt (fun _ => out) hd hpkt] at hr
  cases hr
  have device : (Packets.update w (fun d => {d with rxSkbs := d.rxSkbs.insert id out})).dev =
      some {d with rxSkbs := d.rxSkbs.insert id out} := by simp [Packets.update,hd]
  constructor
  · intro after ha slot k hk valid pid word
    have eq := Option.some.inj (ha.symm.trans device)
    subst after
    exact hi.1.owners d hd slot k hk valid pid word
  · intro after slot packet ha hpacket other k ho hk
    have eq := Option.some.inj (ha.symm.trans device)
    have eq' := Option.some.inj (ho.symm.trans device)
    subst after
    subst other
    by_cases chosen : id = slot
    · subst slot
      have eq : packet = out := by simpa using hpacket.symm
      subst packet
      rw [peer]
      exact hi.1.compatible d id pkt hd hpkt d k hd (by simpa [key] using hk)
    · exact hi.1.compatible d slot packet hd
        (by simpa [Std.TreeMap.getElem?_insert,chosen] using hpacket) d k hd hk
  · intro after ha slot packet hp
    have eq := Option.some.inj (ha.symm.trans device)
    subst after
    by_cases chosen : id = slot
    · subst slot
      have eq : packet = out := by simpa using hp.symm
      subst packet
      rw [key]
      exact hi.1.rxKeys d hd id pkt hpkt
    · exact hi.1.rxKeys d hd slot packet
        (by simpa [Std.TreeMap.getElem?_insert,chosen] using hp)

/-- The original prepare cut consumes the ring, decrypts the stored packet,
and publishes its source-derived replacement before returning the peer loan. -/
theorem prepareSource_preserves :
    Preserves OwnerBounds.Carrier Queues.RxWorkers.prepareSource := by
  have device : Preserves OwnerBounds.Carrier getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi (congrArg WGStoreView.dev ((ProjectedAction.iff_run_ambient _ _ _).mp
        getDev_sameWGStore w a result v b hr))
  have ring (queue : PtrRing SkbId) :
      Preserves OwnerBounds.Carrier (modifyDev fun d => {d with decryptQueue := queue}) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_map)
      _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi
  rw [RxOrigin.prepareSource_factor]
  unfold RxOrigin.prepareWith
  simp only [monadLift_self]
  apply preserves_bind device
  intro dev
  generalize consumed : dev.decryptQueue.consume = item
  rcases item with ⟨item,queue⟩
  cases item with
  | none =>
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed false) OwnerBounds.Carrier)
    intro _
    exact preserves_pure none
  | some id =>
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed true) OwnerBounds.Carrier)
    intro _
    apply preserves_bind (ring queue)
    intro _
    apply hoare_bind _ _ (readDecrypt_spec id)
    intro result
    rcases result with ⟨pkt,decrypted⟩
    let P := fun w => OwnerBounds.Carrier w ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[id]? = some pkt ∧
      ∀ out, decrypted = some out → out.peer = pkt.peer ∧ out.keypair = pkt.keypair
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted decrypted.isSome) P)
    intro yes
    cases yes with
    | false =>
      apply hoare_bind _ _
        (hoare_consequence (publishSource_preserves id .dead)
          (fun _ h => h.1) (fun _ _ h => h))
      intro pid
      exact preserves_pure (some pid)
    | true =>
      cases decrypted with
      | none =>
        exact hoare_consequence (hoare_liftAmbient (AmbientM.invariant "unreachable") P)
          (fun _ h => h) (fun _ _ h => h.1)
      | some out =>
        have write : Hoare (setRxSkb id fun _ => out) P (fun _ w => OwnerBounds.Carrier w) := by
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a value v b hi hr
          obtain ⟨d,hd,hpkt,fields⟩ := hi.2
          obtain ⟨peer,key⟩ := fields out rfl
          exact (hoare_iff_run_ambient _ _ _).mp (replacePacket_spec id pkt out peer key)
            w a value v b ⟨hi.1,d,hd,hpkt⟩ hr
        apply hoare_bind _ _ write
        intro _
        apply preserves_bind (publishSource_preserves id .crypted)
        intro pid
        exact preserves_pure (some pid)

/-- The actual product worker keeps arbitrary IRQ/softirq actions under their
explicit carrier contracts. Its final peer payment may delete a peer. -/
theorem decryptStep_preserves (softirq irq : Leanux.M Unit)
    (hs : Preserves (fun w : World => OwnerBounds.Carrier w.wg) softirq)
    (hi : Preserves (fun w : World => OwnerBounds.Carrier w.wg) irq) :
    Preserves (fun w : World => OwnerBounds.Carrier w.wg) (decryptStep softirq irq) := by
  have native {α : Type} (a : WG.M α) (ha : Preserves OwnerBounds.Carrier a) :
      Preserves (fun w : World => OwnerBounds.Carrier w.wg) (liftWG a) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v hp hr
    rw [liftWG_run] at hr
    cases run : (a.run w.wg).run w.ambient with
    | error e => simp [run,Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨value,g⟩,ambient⟩
      simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
      obtain ⟨rfl,rfl⟩ := hr
      exact (hoare_iff_run_ambient _ _ _).mp ha w.wg w.ambient value g ambient hp run
  rw [← Queues.RxWorkers.decrypt_source]
  unfold Queues.RxWorkers.decryptSource
  apply preserves_bind hs
  intro _
  apply preserves_bind (native _ prepareSource_preserves)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid =>
    exact preserves_bind hi fun _ =>
      preserves_bind (native _ (OwnerConsume.peerPut_preserves (some pid))) fun _ =>
        preserves_bind hs (fun _ => preserves_pure true)

end Leanux.Proofs.WG.OwnerDecrypt
