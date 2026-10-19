import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxConsumptionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollHistoryFrames
import Leanux.Proofs.WG.Queues.HolderDecrypt

/-! The native decrypt prefix carries the exact publication loan from its real
peer increment. Payload and ring changes retain the same holder witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem Upper.decrypt_publish (upper : Upper holders cs loans w)
    (id : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((RxWorkers.publishSource id state).run w).run a = .ok ((pid,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Upper holders cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  rw [DecryptCarrier.publish_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pkt,read,ar,hread,owner,deref,ad,hderef,u,got,ag,hget,x,done,ab,hmid,hpure⟩ := run
  cases u; cases x; cases hpure
  have readEq := (Packets.getRxSkb_current id w read pkt a ar hread).1
  subst read
  have derefEq := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (fun z => z=w)) w ar pid deref ad rfl hderef
  subst deref
  obtain ⟨d,p,hd,hp,pos,handoff⟩ := peerGet_handoff ad ag hget
  obtain ⟨dd,pp,hdd,hpp,hpos,effect⟩ := peerGet_loan pid w got ad ag hget
  have loan : Loan w (some pid) got := by
    refine ⟨dd,pp,hdd,hpp,hpos,?_,handoff.rx⟩
    have dev := congrArg WGStoreView.dev effect
    change got.dev = some {dd with peers := dd.peers.insert pid {pp with refcount := pp.refcount + 1}} at dev
    simp only [peerView,creditWorld,dev,Option.map_some,Option.bind_some]
  obtain ⟨dd,pp,hdd,hpp,hpos,acquired⟩ := upper.loan loan
  exact ⟨dd,pp,hdd,hpp,hpos,acquired.peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (publicationMiddle_frame pid id state) got ag () v b hmid)⟩

theorem Phased.decrypt_publish (account : Phased holders cs loans w)
    (id : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((RxWorkers.publishSource id state).run w).run a = .ok ((pid,v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Phased holders cs (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,hd,hp,pos,upper⟩ := account.upper.decrypt_publish id state a b run
  obtain ⟨dd,pp,hdd,hpp,_,carriers⟩ := DecryptCarrier.publish_state id state account.funded.carriers a b run
  have eqd : dd=d := Option.some.inj (hdd.symm.trans hd)
  subst dd
  have eqp : pp=p := Option.some.inj (hpp.symm.trans hp)
  subst pp
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderDecrypt.publish_frame id state w)
    w a pid v b (Frame.refl w) run
  exact ⟨d,p,hd,hp,pos,⟨account.funded.aligned.frame frame,
    WorkReservations.carrier_loans_perm carriers List.perm_middle.symm⟩,upper⟩

theorem Phased.decrypt_ring (account : Phased holders cs loans w) (ring : PtrRing SkbId) :
    Phased holders cs loans {w with dev := w.dev.map fun d => {d with decryptQueue := ring}} := by
  have frame : Frame w {w with dev := w.dev.map fun d => {d with decryptQueue := ring}} := by
    constructor
    · cases hd : w.dev <;> simp [passiveView,hd]
    · cases hd : w.dev <;> simp [sendView,hd]
    · intro pid batches found
      have same : handoffTxView {w with dev := w.dev.map fun d => {d with decryptQueue := ring}} = handoffTxView w := by
        funext q
        cases hd : w.dev <;> simp [handoffTxView,hd]
      rw [same] at found
      exact found
  have peers : peerView {w with dev := w.dev.map fun d => {d with decryptQueue := ring}} = peerView w := by
    cases hd : w.dev <;> simp [peerView,hd]
  exact ⟨⟨account.funded.aligned.frame frame,DecryptCarrier.ring_state account.funded.carriers ring⟩,
    account.upper.peer_view peers⟩

theorem Phased.decrypt_read (account : Phased holders cs loans w) (id : SkbId) (a b : Ambient)
    (run : ((RxOrigin.readDecrypt id).run w).run a = .ok (((pkt,result),v),b)) :
    Phased holders cs loans v ∧ (∃ d, v.dev=some d ∧ d.rxSkbs[id]?=some pkt) ∧
      ∀ out, result=some out → out.peer=pkt.peer ∧ out.keypair=pkt.keypair := by
  obtain ⟨carriers,stored,fields⟩ := DecryptCarrier.readDecrypt_state id account.funded.carriers a b run
  unfold RxOrigin.readDecrypt at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨old,read,ar,hread,decrypted,done,ad,hdecrypt,hpure⟩ := run
  cases hpure
  have readEq := (Packets.getRxSkb_current id w read pkt a ar hread).1
  subst read
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderDecrypt.decryptPacket_frame pkt w)
    w ar result v b (Frame.refl w) hdecrypt
  have peer := congrArg (fun p => p.1.1)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (DecryptCarrier.decryptPacket_view pkt) w ar result v b hdecrypt)
  exact ⟨⟨⟨account.funded.aligned.frame frame,carriers⟩,account.upper.peer_view peer⟩,stored,fields⟩

theorem Phased.decrypt_payload (account : Phased holders cs loans w)
    {id : SkbId} {old out : RxPacket} (hd : w.dev=some d) (hp : d.rxSkbs[id]?=some old)
    (peer : out.peer=old.peer) (key : out.keypair=old.keypair)
    (a b : Ambient) (run : ((setRxSkb id (fun _ => out)).run w).run a=.ok (((),v),b)) :
    Phased holders cs loans v := by
  have carriers := DecryptCarrier.set_payload_state account.funded.carriers hd hp peer key a b run
  rw [Packets.setRxSkb_run w a d id old (fun _ => out) hd hp] at run
  cases run
  have frame : Frame w (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) := by
    constructor
    · simp [passiveView,Packets.update,hd]
    · simp [sendView,Packets.update,hd]
    · intro pid batches found
      simpa [handoffTxView,Packets.update,hd] using found
  have peers : peerView (Packets.update w fun d => {d with rxSkbs := d.rxSkbs.insert id out}) = peerView w := by
    simp [peerView,Packets.update,hd]
  exact ⟨⟨account.funded.aligned.frame frame,carriers⟩,account.upper.peer_view peers⟩

theorem Phased.decrypt_prepare (account : Phased holders cs loans w) (a b : Ambient)
    (run : ((RxWorkers.prepareSource).run w).run a=.ok ((result,v),b)) :
    match result with
    | none => Phased holders cs loans v
    | some pid => ∃ o : Owner, o.slot=pid ∧ Phased holders cs (o::loans) v := by
  rw [DecryptCarrier.prepare_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,ar,hget,tail⟩ := run
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
      exact account
    | some id =>
      simp only [hc,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨value,after,aa,hbranch,u,ringWorld,ab,hring,pair,readWorld,ac,hread,decision,decWorld,ad,hdecision,tail⟩ := tail
      change Except.ok ((true,w),CounterWindow.record a .decWorkerConsumed true)=Except.ok ((value,after),aa) at hbranch
      cases hbranch
      cases hring
      rcases pair with ⟨pkt,decrypted⟩
      have hiRing := account.decrypt_ring ring
      obtain ⟨hiRead,⟨dev,hdev,hpkt⟩,fields⟩ := hiRing.decrypt_read id _ ac hread
      change Except.ok ((decrypted.isSome,readWorld),CounterWindow.record ac .decWorkerDecrypted decrypted.isSome)=
        Except.ok ((decision,decWorld),ad) at hdecision
      cases hdecision
      cases decrypted with
      | none =>
        simp only [Option.isSome_none,Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨pid,final,af,hpublish,hpure⟩ := tail
        cases hpure
        obtain ⟨d,p,_,_,_,state⟩ := hiRead.decrypt_publish id .dead _ b hpublish
        exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,state⟩
      | some out =>
        simp only [Option.isSome_some,ite_true,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨u,updated,au,hwrite,pid,final,af,hpublish,hpure⟩ := tail
        cases u
        cases hpure
        have hiWrite := hiRead.decrypt_payload hdev hpkt (fields out rfl).1 (fields out rfl).2 _ au hwrite
        obtain ⟨d,p,_,_,_,state⟩ := hiWrite.decrypt_publish id .crypted _ b hpublish
        exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,state⟩

theorem ExactBoundary.decrypt_prepare (account : ExactBoundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (result,v),k)) :
    match result with
    | none => ExactBoundary cs loans v.wg
    | some pid => ∃ o : Owner, o.slot=pid ∧ ExactBoundary cs (o::loans) v.wg := by
  obtain ⟨holders,account⟩ := account
  have native := DecryptIteration.native_normal Origins.HistoryAdapters.prepare_erases run
  have prepared := account.phased.decrypt_prepare w.ambient v.ambient native
  obtain ⟨epoch,n,ringHistory,ring⟩ := physical
  have stable := DecryptStable.prepare_stable account.funded.carriers account.stable ring w.ambient v.ambient native
  cases result with
  | none => exact ⟨holders,prepared.boundary stable⟩
  | some pid =>
    obtain ⟨owner,slot,prepared⟩ := prepared
    exact ⟨owner,slot,holders,prepared.boundary stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
