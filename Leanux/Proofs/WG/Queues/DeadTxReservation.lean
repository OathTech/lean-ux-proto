import Leanux.Proofs.WG.Queues.TxReservation

/-! A DEAD logical TX head reaches disposal through the original peek and
drop. One source-supplied reservation is charged for the whole batch; neither
an earlier EPIPE event nor eventual worker scheduling is assumed here. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem queue_update (hi : ClearWork.Inv cs loans w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (q : PrevQueue (List SkbId)) :
    ClearWork.Inv cs loans {w with dev := some {d with peers := d.peers.insert pid {p with txQueue := q}}} :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.peer_update)
    hi hd hp {p with txQueue := q} rfl rfl rfl rfl (fun _ h => h)

private theorem dead_read (head : TxDisposition.HeadState first .dead w)
    (a b : Ambient) (hr : ((getTxSkb first).run w).run a = .ok ((pkt,v),b)) :
    v = w ∧ pkt.state = .dead := by
  obtain ⟨rfl,_,d,hd,hp⟩ := Packets.getTxSkb_current first w v pkt a b hr
  obtain ⟨old,stored,state⟩ := head
  have same : old = pkt := by simpa [TxDisposition.txPackets,hd,hp] using stored.symm
  subst old
  exact ⟨rfl,state⟩

/-- The actual DEAD body drops the selected batch before paying its supplied
reservation. Normal final peer erasure is allowed. -/
theorem dead_body_normal (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource o.slot (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) : result = true ∧ ClearWork.Inv cs loans v := by
  unfold TxDisposition.bodySource at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨go,checked,ac,hgo,hr⟩ := hr
  have hg : go = true ∧ checked = w := by
    change (((do
      let packet ← getTxSkb first
      branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
        (CounterWindow.record a .txPacket true)) = .ok ((go,checked),ac) at hgo
    rw [MaterialOrigin.bind_ok_ambient] at hgo
    obtain ⟨pkt,read,ar,hread,hbranch⟩ := hgo
    obtain ⟨readEq,dead⟩ := dead_read head _ _ hread
    subst read
    simp only [dead] at hbranch
    cases hbranch
    exact ⟨rfl,rfl⟩
  obtain ⟨goEq,checkedEq⟩ := hg
  subst go
  subst checked
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,List.head?_cons,bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,dead⟩ := dead_read head ac ar hread
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨saved,s₁,a₁,h₁,hr⟩ := hr
  obtain ⟨s₁Eq,a₁Eq,d,hd,hp⟩ := getPeer_normal o.slot w s₁ saved ar a₁ h₁
  subst s₁
  subst a₁
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,s₂,a₂,h₂,hr⟩ := hr
  obtain ⟨s₂Eq,a₂Eq,d₂,hd₂,hp₂⟩ := getPeer_normal o.slot w s₂ current ar a₂ h₂
  subst s₂
  subst a₂
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = saved := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,dropped,ad,hdrop,hr⟩ := hr
  cases u
  have inv : ClearWork.Inv cs (o :: loans) dropped := by
    cases hdrop
    simpa only [setPeer,modifyDev,hd,Option.map_some] using
      queue_update hi hd hp saved.txQueue.dropPeeked
  simp only [dead] at hr
  change ((TxDisposition.disposeSource o.slot (first :: rest) pkt.keypair).run dropped).run
      (CounterWindow.record ad .txCrypted false) = .ok ((result,v),b) at hr
  exact dispose_normal o (first :: rest) pkt.keypair inv _ b hr

/-- At the actual worker entry, the supplied owner funds one logical head
batch. The peek's cached representation does not create a second reservation. -/
theorem dead_step_normal (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v := by
  rw [← TxDisposition.stepSource_eq] at hr
  unfold TxDisposition.stepSource at hr
  simp only [bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d,hd,hp⟩ := getPeer_normal o.slot w read p a ar hread
  subst read
  subst ar
  obtain ⟨old,residentOld,hhead⟩ := queue
  obtain ⟨before,hbefore,_,hold,_⟩ := resident_fields residentOld
  have de : before = d := Option.some.inj (hbefore.symm.trans hd)
  subst before
  have pe : old = p := Option.some.inj (hold.symm.trans hp)
  subst old
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨⟨selected,q⟩,peeked,ap,hpeek,hr⟩ := hr
  obtain ⟨selectedEq,_,_,peekedEq⟩ := prev_peek_normal p.txQueue w peeked a ap selected q hpeek
  subst peeked
  have chosen : selected = some (first :: rest) := selectedEq.trans hhead
  subst selected
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d₂,hd₂,hp₂⟩ := getPeer_normal o.slot w read current ap ar hread
  subst read
  subst ar
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = p := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,installed,ai,hset,hr⟩ := hr
  cases u
  have next : ClearWork.Inv cs (o :: loans) installed ∧
      TxDisposition.HeadState first .dead installed := by
    cases hset
    constructor
    · simpa only [setPeer,modifyDev,hd,Option.map_some] using queue_update hi hd hp q
    · simpa [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd] using head
  exact dead_body_normal o first rest next.1 next.2 ai b (by simpa only [hhead] using hr)

/-- The complete DEAD-head worker step pays its single supplied reservation,
removes every packet in that batch, and performs no socket send. -/
theorem dead_step_endpoint (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v ∧
      (∀ id ∈ first :: rest, TxDisposition.txPackets v id = none) ∧ v.sent = w.sent := by
  have account := dead_step_normal o first rest hi queue head a b hr
  have queued : ∃ p, PeerBorrow.resident (wgStoreView w) o.slot = some p ∧
      p.txQueue.all.head? = some (first :: rest) := by
    obtain ⟨p,residentOld,hhead⟩ := queue
    obtain ⟨d,hd,_,hp,_⟩ := resident_fields residentOld
    exact ⟨p,by simp [PeerBorrow.resident,wgStoreView,hd,hp],hhead⟩
  have cells := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.dead_step_endpoint o.slot first rest w.sent)
    w a result v b ⟨queued,head,rfl⟩ hr
  exact ⟨account.1,account.2,cells.2⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
