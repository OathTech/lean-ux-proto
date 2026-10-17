import Leanux.Proofs.WG.Queues.TxCompletionQueues

/-! The actual CRYPTED head sends, keeps its freshness handoff charged, and
then pays one supplied batch reservation. Normal final peer erasure is allowed;
negative socket errno does not skip the remaining source disposal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem crypted_read (head : TxDisposition.HeadState first .crypted w)
    (a b : Ambient) (hr : ((getTxSkb first).run w).run a = .ok ((pkt,v),b)) :
    v = w ∧ pkt.state = .crypted := by
  obtain ⟨rfl,_,d,hd,hp⟩ := Packets.getTxSkb_current first w v pkt a b hr
  obtain ⟨old,stored,state⟩ := head
  have same : old = pkt := by simpa [TxDisposition.txPackets,hd,hp] using stored.symm
  subst old
  exact ⟨rfl,state⟩

/-- The actual CRYPTED body drops the selected batch before paying its supplied
reservation. Normal final peer erasure is allowed. -/
theorem crypted_body_send_only (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource o.slot (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) : result = true ∧ ∃ delta : HandoffDelta,
      delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
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
    obtain ⟨readEq,dead⟩ := crypted_read head _ _ hread
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
  obtain ⟨readEq,dead⟩ := crypted_read head ac ar hread
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
      (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.queue_update)
        hi hd hp saved.txQueue.dropPeeked
  simp only [dead] at hr
  change (((do
      createDataDone o.slot (first :: rest)
      TxDisposition.disposeSource o.slot (first :: rest) pkt.keypair) : WG.M Bool).run dropped).run
      (CounterWindow.record ad .txCrypted true) = .ok ((result,v),b) at hr
  obtain ⟨resultEq,delta,noTx,funded,sends⟩ :=
    completion_dispose_send_only o (first :: rest) pkt.keypair inv _ b hr
  have frame : sendView dropped = sendView w := by
    cases hdrop
    simp only [sendView,hd,Option.map_some]
  exact ⟨resultEq,delta,noTx,funded,by rw [sends,frame]⟩

/-- At the actual worker entry, the supplied owner funds one logical head
batch. The peek's cached representation does not create a second reservation. -/
theorem crypted_step_send_only (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
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
      TxDisposition.HeadState first .crypted installed := by
    cases hset
    constructor
    · simpa only [setPeer,modifyDev,hd,Option.map_some] using
      (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.queue_update) hi hd hp q
    · simpa [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd] using head
  obtain ⟨resultEq,delta,noTx,funded,sends⟩ :=
    crypted_body_send_only o first rest next.1 next.2 ai b (by simpa only [hhead] using hr)
  have frame : sendView installed = sendView w := by
    cases hset
    simp only [sendView,hd,Option.map_some]
  exact ⟨resultEq,delta,noTx,funded,by rw [sends,frame]⟩

theorem crypted_body_normal (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource o.slot (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) : result = true ∧ ∃ delta : HandoffDelta,
      ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
  obtain ⟨resultEq,delta,_,funded,sends⟩ := crypted_body_send_only o first rest hi head a b hr
  exact ⟨resultEq,delta,funded,sends⟩

theorem crypted_step_normal (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
  obtain ⟨resultEq,delta,_,funded,sends⟩ := crypted_step_send_only o first rest hi queue head a b hr
  exact ⟨resultEq,delta,funded,sends⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
