import Leanux.Proofs.WG.Queues.RxIngressStable

/-! Stable-boundary cuts for the actual receive poll. The selected packet is
removed from the stable ledger only after the readiness test establishes that
it is not uncrypted. Final NAPI completion requires the actual stopped-head
fact; carrier funding alone does not establish that fact. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

theorem StableRx.perm (hs : StableRx cs w) (he : cs.Perm ds) : StableRx ds w := by
  refine ⟨fun c hc => hs.queued c (he.mem_iff.mpr hc), ?_, hs.cold⟩
  intro d hd
  exact (hs.ring d hd).trans ((he.filter _).map _)

theorem uncrypted_remaining (cs : Ledger) (removed : List Packet) (w : WGWorld)
    (hr : ∀ p ∈ removed, (packetAt w p).any (fun pkt => pkt.state == .uncrypted) = false) :
    uncrypted (remaining cs removed) w = uncrypted cs w := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hm : c.packet ∈ removed
    · have hc := hr c.packet hm
      simpa [remaining, uncrypted, hm, hc] using ih
    · by_cases hu : (packetAt w c.packet).any (fun pkt => pkt.state == .uncrypted) = true
      · simpa [remaining, uncrypted, hm, hu] using congrArg (c.packet :: ·) ih
      · simpa [remaining, uncrypted, hm, hu] using ih

theorem StableRx.remaining_ready (hs : StableRx cs w)
    (hr : ∀ p ∈ removed, (packetAt w p).any (fun pkt => pkt.state == .uncrypted) = false) :
    StableRx (remaining cs removed) w := by
  refine ⟨fun c hc => hs.queued c (List.mem_filter.mp hc).1, ?_, hs.cold⟩
  intro d hd
  rw [uncrypted_remaining cs removed w hr]
  exact hs.ring d hd

/-- Queue representation may change at peek, provided its logical contents do
not. This is weaker than equality of the physical cached-head representation. -/
theorem StableRx.queue_same (hs : StableRx cs w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (q : PrevQueue SkbId) (hq : q.all = p.rxQueue.all) :
    StableRx cs {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := q}}} := by
  refine ⟨hs.queued, ?_, ?_⟩
  · intro out ho
    cases ho
    simpa [uncrypted,packetAt,hd] using hs.ring d hd
  · intro out k peer id ho hk cold head
    cases ho
    by_cases same : pid = k
    · subst k
      have eq : peer = {p with rxQueue := q} := by simpa using hk.symm
      subst peer
      exact hs.cold d pid p id hd hp cold (hq ▸ head)
    · exact hs.cold d k peer id hd
        (by simpa [Std.TreeMap.getElem?_insert,same] using hk) cold head

/-- An active peer may expose a new ready head after a removal. A cold peer
cannot take this branch from a stable boundary. -/
theorem StableRx.queue_hot {p : Peer} {pid : PeerId} (hs : StableRx cs w) (hd : w.dev = some d)
    (hot : p.napiScheduled = true) (q : PrevQueue SkbId) :
    StableRx cs {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := q}}} := by
  refine ⟨hs.queued, ?_, ?_⟩
  · intro out ho
    cases ho
    simpa [uncrypted,packetAt,hd] using hs.ring d hd
  · intro out k peer id ho hk cold head
    cases ho
    by_cases same : pid = k
    · subst k
      have eq : peer = {p with rxQueue := q} := by simpa using hk.symm
      subst peer
      simp only [hot, Bool.true_eq_false] at cold
    · exact hs.cold d k peer id hd
        (by simpa [Std.TreeMap.getElem?_insert,same] using hk) cold head

/-- The native source drop preserves the stable remaining ledger. The exact
packet-state premise is supplied by the preceding actual readiness getter. -/
theorem StableRx.drop_ready {id : SkbId} {pkt : RxPacket} (hs : StableRx cs w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (peek : p.rxQueue.peeked = some id)
    (stored : d.rxSkbs[id]? = some pkt) (ready : pkt.state ≠ .uncrypted)
    (ambient ambient' : Ambient)
    (run : ((dropRxQueue pid).run w).run ambient = .ok (((),v),ambient')) :
    StableRx (remaining cs [⟨d.ifindex,id⟩]) v := by
  have hot : p.napiScheduled = true := by
    cases hn : p.napiScheduled
    · obtain ⟨q,hq,hu⟩ := hs.cold d pid p id hd hp hn (by simp [PrevQueue.all,peek])
      rw [stored] at hq
      cases hq
      exact (ready hu).elim
    · rfl
  have noRing : ∀ x ∈ ([⟨d.ifindex,id⟩] : List Packet),
      (packetAt w x).any (fun packet => packet.state == .uncrypted) = false := by
    intro x hx
    have eq : x = ⟨d.ifindex,id⟩ := by simpa using hx
    subst x
    simp [packetAt,hd,stored]
    cases ht : pkt.state <;> simp_all <;> rfl
  have endpoint : v = {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := p.rxQueue.dropPeeked}}} := by
    have h := run
    simp [dropRxQueue,getPeer,getDev,setPeer,modifyDev,hd,hp] at h
    exact h.1.symm
  rw [endpoint]
  exact (hs.remaining_ready noRing).queue_hot hd hot _

/-- The stopped readiness test's state assertion, independent of the current
NAPI bit. It is what permits the later source completion write. -/
def ColdHead (pid : PeerId) (w : WGWorld) : Prop :=
  ∀ d p id, w.dev = some d → d.peers[pid]? = some p → p.rxQueue.all.head? = some id →
    ∃ pkt : RxPacket, d.rxSkbs[id]? = some pkt ∧ pkt.state = .uncrypted

theorem StableRx.complete (hs : StableRx cs w) (hc : ColdHead pid w)
    (ambient ambient' : Ambient)
    (run : ((completeRxQueue pid).run w).run ambient = .ok (((),v),ambient')) :
    StableRx cs v := by
  unfold completeRxQueue at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,a,aa,hget,hset⟩ := run
  obtain ⟨ha,haa,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hget
  subst a
  subst aa
  have endpoint : v = {w with dev := some {d with peers := d.peers.insert pid {p with napiScheduled := false}}} := by
    cases hset
    simp [hd]
  rw [endpoint]
  refine ⟨hs.queued, ?_, ?_⟩
  · intro out ho
    cases ho
    simpa [uncrypted,packetAt,hd] using hs.ring d hd
  · intro out k peer id ho hk cold head
    cases ho
    by_cases same : pid = k
    · subst k
      have eq : peer = {p with napiScheduled := false} := by simpa using hk.symm
      subst peer
      exact hc d p id hd hp head
    · exact hs.cold d k peer id hd
        (by simpa [Std.TreeMap.getElem?_insert,same] using hk) cold head

/-- Peek runs both original peer getters and keeps the logical queue unchanged. -/
theorem stable_peek (pid : PeerId) (hs : StableRx cs w)
    (ambient ambient' : Ambient)
    (run : ((peekRxQueue pid).run w).run ambient = .ok ((first,v),ambient')) :
    StableRx cs v := by
  unfold peekRxQueue at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,a,aa,hget,rest⟩ := run
  obtain ⟨ha,haa,d,hd,hp⟩ := getPeer_normal pid w a p ambient aa hget
  subst a; subst aa
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨out,b,ab,hpeek,rest⟩ := rest
  rcases out with ⟨head,q⟩
  obtain ⟨_,hall,_,hb⟩ := prev_peek_normal p.rxQueue w b ambient ab head q hpeek
  subst b
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨p2,a,aa,hget2,rest⟩ := rest
  obtain ⟨ha,haa,d2,hd2,hp2⟩ := getPeer_normal pid w a p2 ab aa hget2
  subst a; subst aa
  have deq : d2 = d := by rw [hd] at hd2; cases hd2; rfl
  subst d2
  have peq : p2 = p := by rw [hp] at hp2; cases hp2; rfl
  subst p2
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,a,aa,hset,rest⟩ := rest
  cases u
  simp only [StateT.run_pure] at rest
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest
  have endpoint : v = {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := q}}} := by
    cases hset
    simp [hd]
  rw [endpoint]
  exact hs.queue_same hd hp q hall

/-- Normal cleanup leaves the same stable remainder. The selected charge is
paid and its cell freed; the actual payment may erase its peer. -/
theorem stable_selected_cleanup (hs : StableRx cs w)
    (hi : CarrierState (c :: cs) loans w) (phase : c.phase = .selected)
    (owner : pkt.peer = c.owner.slot) (ambient ambient' : Ambient)
    (run : ((cleanup c.packet.slot pkt flag).run w).run ambient = .ok (((),v),ambient')) :
    StableRx cs v := by
  unfold cleanup at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,a,aa,hkey,rest⟩ := run
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,b,ab,hpeer,rest⟩ := rest
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ret,z,az,hbranch,hfree⟩ := rest
  have ha := keyPut_state _ _ hi ambient aa hkey
  obtain ⟨p,hp,_⟩ := selected_credit ha.funded phase
  obtain ⟨d,hd,_,hpid,_⟩ := resident_fields hp
  have payment : ((peerPut (some c.owner.slot)).run a).run aa = .ok (((),b),ab) := by
    simpa only [owner] using hpeer
  have rx := (peerPut_effect _ a b d p aa ab hd hpid payment).2.2
  have ib := inventory_paid (inventory_view ha.inventory rx)
  have qb := selected_payment_queues ha.queues phase hd hpid aa ab payment
  have stable := (hs.view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (stable_keypairPut (some pkt.keypair) false) w ambient () a aa hkey)).put aa ab hpeer
  have hz := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (fun g => g = b))
    b ab ret z az rfl hbranch
  subst z
  exact stable.free ib qb (by simp [paid]) az ambient' hfree

/-- The readiness test is read-only in WG state, and its result is the actual
stored packet-state comparison. Failed getters still have no normal endpoint. -/
theorem ready_result (first : Option SkbId) (w v : WGWorld) (go : Bool)
    (ambient ambient' : Ambient)
    (run : ((WG.andM (branch .rxPollPacket first.isSome) do
      let some id := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb id).state != .uncrypted)).run w).run ambient =
        .ok ((go,v),ambient')) :
    v = w ∧ match first with
      | none => go = false
      | some id => ∃ d pkt, w.dev = some d ∧ d.rxSkbs[id]? = some pkt ∧
          go = (pkt.state != .uncrypted) := by
  cases first with
  | none =>
    change Except.ok ((false,w),CounterWindow.record ambient .rxPollPacket false) =
      .ok ((go,v),ambient') at run
    cases run
    exact ⟨rfl,rfl⟩
  | some id =>
    change ((getRxSkb id >>= fun pkt => branch .rxPollNotUncrypted (pkt.state != .uncrypted)).run w).run
      (CounterWindow.record ambient .rxPollPacket true) = .ok ((go,v),ambient') at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨pkt,u,au,hget,hbranch⟩ := run
    obtain ⟨hu,_,d,hd,hpkt⟩ := Packets.getRxSkb_current id w u pkt _ au hget
    subst u
    change Except.ok (((pkt.state != .uncrypted),w),
      CounterWindow.record au .rxPollNotUncrypted (pkt.state != .uncrypted)) =
      .ok ((go,v),ambient') at hbranch
    cases hbranch
    exact ⟨rfl,d,pkt,hd,hpkt,rfl⟩

/-- The normal peek supplies a head fact about the post-peek queue, including
the empty case where a cached-head fact alone would be insufficient. -/
theorem peek_head (pid : PeerId) (w v : WGWorld) (first : Option SkbId)
    (ambient ambient' : Ambient)
    (run : ((peekRxQueue pid).run w).run ambient = .ok ((first,v),ambient')) :
    ∀ d p, v.dev = some d → d.peers[pid]? = some p → first = p.rxQueue.all.head? := by
  obtain ⟨before,after,_,ha,_,_,hall,_,head⟩ :=
    peekRxQueue_normal pid w v first ambient ambient' run
  intro d p hd hp
  have cell := rxQueues_at v d pid p hd hp
  rw [ha] at cell
  have same : after = ⟨d.ifindex,p.internalId,p.rxQueue⟩ := Option.some.inj cell
  rw [same] at hall
  exact head.trans (congrArg List.head? hall.symm)

/-- A false recorded readiness result proves the exact cold-head condition
needed by completion. No packet-state fact is inferred from a journal label. -/
theorem ready_false_cold (pid : PeerId) (first : Option SkbId)
    (head : ∀ d p, w.dev = some d → d.peers[pid]? = some p → first = p.rxQueue.all.head?)
    (ambient ambient' : Ambient)
    (run : ((WG.andM (branch .rxPollPacket first.isSome) do
      let some id := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb id).state != .uncrypted)).run w).run ambient =
        .ok ((false,v),ambient')) : ColdHead pid v := by
  obtain ⟨hv,result⟩ := ready_result first w v false ambient ambient' run
  subst v
  intro d p id hd hp hh
  have firstEq : first = some id := (head d p hd hp).trans hh
  subst first
  dsimp only at result
  obtain ⟨old,pkt,hold,hpkt,hstate⟩ := result
  have same : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  refine ⟨pkt,hpkt,?_⟩
  cases hs : pkt.state with
  | uncrypted => rfl
  | crypted => rw [hs] at hstate; cases hstate
  | dead => rw [hs] at hstate; cases hstate

theorem ready_true_packet {id : SkbId} {pkt : RxPacket}
    (hd : w.dev = some d) (stored : d.rxSkbs[id]? = some pkt)
    (ambient ambient' : Ambient)
    (run : ((WG.andM (branch .rxPollPacket (some id).isSome) do
      let some f := some id | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)).run w).run ambient =
        .ok ((true,v),ambient')) : pkt.state ≠ .uncrypted := by
  obtain ⟨_,old,q,hold,hq,hstate⟩ := ready_result (some id) w v true ambient ambient' run
  have same : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  rw [stored] at hq
  cases hq
  intro hu
  rw [hu] at hstate
  cases hstate

/-- The new stable remainder uses the exact removed-stamp suffix of the
unchanged poll observer. A Stop still keeps its actual journal; no stable
returned state is fabricated for it. -/
theorem stable_drop_observed (initial : Ledger) (loans : Reservations)
    (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (ready : pkt.state ≠ .uncrypted) :
    PrefixEnsures (fun h w => PollCarrier.Captured initial loans pid skb (pkt,stamp) h w ∧
      StableRx (PollCarrier.rest initial h) w.wg) (fun _ => True)
      (RxJoint.drop pid n skb stamp)
      (fun _ h w => PollCarrier.Live initial loans pid skb stamp pkt h w ∧
        StableRx (PollCarrier.rest initial h) w.wg) := by
  apply PollCarrier.normal_spec ((RxJoint.access_appends _).bind (fun _ => RxJoint.emit_appends _))
  intro w h u v hi run
  have live := (PollCarrier.drop_observed initial loans pid n skb stamp pkt w h hi.1).choose_spec.2.2
  simp only [RxJoint.drop] at live
  rw [run] at live
  refine ⟨live,?_⟩
  simp only [runPrefix_bind] at run ⊢
  cases ha : runPrefix (RxJoint.access (liftWGObserver (rxDropPeekedPrefix pid))) w h with
  | mk result t => cases result with
    | error e => simp [ha] at run
    | ok result =>
      rcases result with ⟨u0,a⟩
      cases u0
      simp only [ha,runPrefix_emit,Except.ok.injEq,Prod.mk.injEq] at run
      have av := run.2
      subst a
      simp only [runPrefix_emit]
      obtain ⟨d,p,hd,hp,hpeek⟩ := hi.1.1.2
      have stampEq : stamp = (d.ifindex,skb+1) := by
        simpa [packetStamp,hd] using hi.1.2.1.symm
      have stored : d.rxSkbs[skb]? = some pkt := by
        simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,hd] using hi.1.2.2
      have original : (liftWG (dropRxQueue pid)).run w = .ok ((),v) :=
        (RxJoint.access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)) w h).symm.trans
          (congrArg Prod.fst ha)
      have stable := hi.2.drop_ready hd hp hpeek stored ready w.ambient v.ambient
        ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ w v () original)
      have frame : PollCarrier.removedPackets t = PollCarrier.removedPackets h := by
        simpa only [ha] using PollCarrier.removed_frame
          (PollCarrier.access_removed (liftWGObserver (rxDropPeekedPrefix pid))) w h
      have removed : PollCarrier.removedPackets (t ++ [.removed n skb stamp]) =
          PollCarrier.removedPackets h ++ [⟨d.ifindex,skb⟩] := by
        simpa [PollCarrier.removedPackets,RxJoint.removedStamps,List.filterMap_append,
          RxJoint.removedStamp,stampEq,PollCarrier.packetOfStamp] using
          congrArg (fun xs => xs ++ [⟨d.ifindex,skb⟩]) frame
      change StableRx (remaining initial (PollCarrier.removedPackets (t ++ [.removed n skb stamp]))) v.wg
      rw [removed,remaining_append]
      exact stable

end Leanux.Proofs.WG.Queues.RxCredits
