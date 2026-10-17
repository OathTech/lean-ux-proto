import Leanux.Proofs.WG.Queues.CryptedTxReservation
import Leanux.Proofs.WG.Queues.TxQueueDebit

namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem logical_factor (w : WGWorld) (pid : PeerId) :
    handoffTxView w pid = (TxDisposition.txQueues w pid).map (·.all) := by
  simp [handoffTxView,TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,
    Option.map_map,Function.comp_def]

private theorem dispose_logical_queues (pid : PeerId) (item : List SkbId) (key : KeypairId)
    (a b : Ambient)
    (hr : ((TxDisposition.disposeSource pid item key).run w).run a = .ok ((result,v),b)) :
    (∀ other, other ≠ pid → handoffTxView v other = handoffTxView w other) ∧
    (∀ q, handoffTxView v pid = some q → handoffTxView w pid = some q) := by
  obtain ⟨others,survives⟩ := dispose_queues pid item key a b hr
  constructor
  · intro q ne
    rw [logical_factor,logical_factor,others q ne]
  · intro q hq
    rw [logical_factor] at hq
    cases hv : TxDisposition.txQueues v pid with
    | none => simp [hv] at hq
    | some old =>
      have same : old.all = q := by simpa [hv] using hq
      rw [logical_factor,survives old hv]
      exact congrArg some same

theorem crypted_body_queues (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource pid (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) :
    (∀ other, other ≠ pid → handoffTxView v other = handoffTxView w other) ∧
      (∀ q, handoffTxView v pid = some q →
        ∃ old, TxDisposition.txQueues w pid = some old ∧ q = old.dropPeeked.all) := by
  unfold TxDisposition.bodySource at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨go,checked,ac,hgo,hr⟩ := hr
  have hg : go = true ∧ checked = w := by
    change (((do
      let packet ← getTxSkb first
      branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
        (CounterWindow.record a .txPacket true)) = .ok ((go,checked),ac) at hgo
    rw [MaterialOrigin.bind_ok_ambient] at hgo
    obtain ⟨pkt,readWorld,ar,hread,hbranch⟩ := hgo
    obtain ⟨readEq,state⟩ :=
      crypted_read
        head _ _ hread
    subst readWorld
    simp only [state] at hbranch
    cases hbranch
    exact ⟨rfl,rfl⟩
  obtain ⟨goEq,checkedEq⟩ := hg
  subst go
  subst checked
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,List.head?_cons,bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,readWorld,ar,hread,hr⟩ := hr
  obtain ⟨readEq,state⟩ :=
    crypted_read
      head ac ar hread
  subst readWorld
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨saved,s₁,a₁,h₁,hr⟩ := hr
  obtain ⟨s₁Eq,a₁Eq,d,hd,hp⟩ := getPeer_normal pid w s₁ saved ar a₁ h₁
  subst s₁
  subst a₁
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,s₂,a₂,h₂,hr⟩ := hr
  obtain ⟨s₂Eq,a₂Eq,d₂,hd₂,hp₂⟩ := getPeer_normal pid w s₂ current ar a₂ h₂
  subst s₂
  subst a₂
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = saved := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,dropped,ad,hdrop,hr⟩ := hr
  cases u
  have dropView : handoffTxView dropped = fun q =>
      if pid = q then some saved.txQueue.dropPeeked.all else handoffTxView w q := by
    cases hdrop
    funext q
    by_cases chosen : pid = q <;>
      simp [handoffTxView,hd,Std.TreeMap.getElem?_insert,chosen]
  simp only [state] at hr
  change (((do
      createDataDone pid (first :: rest)
      TxDisposition.disposeSource pid (first :: rest) pkt.keypair) : WG.M Bool).run dropped).run
      (CounterWindow.record ad .txCrypted true) = .ok ((result,v),b) at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,completed,ac,hcomplete,hdispose⟩ := hr
  cases u
  have completeView := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_queues pid (first :: rest)) dropped _ () completed ac hcomplete
  obtain ⟨others,survivor⟩ := dispose_logical_queues pid (first :: rest) pkt.keypair ac b hdispose
  constructor
  · intro q ne
    rw [others q ne,completeView,dropView]
    simp [Ne.symm ne]
  · intro q hq
    have droppedQueue := survivor q hq
    rw [completeView,dropView] at droppedQueue
    have same : q = saved.txQueue.dropPeeked.all := by simpa using droppedQueue.symm
    exact ⟨saved.txQueue,by simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,hd,hp],same⟩


theorem crypted_step_queues (o : Owner) (first : SkbId) (rest : List SkbId)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    (∀ other, other ≠ o.slot → handoffTxView v other = handoffTxView w other) ∧
      (∀ before after, handoffTxView w o.slot = some before →
        handoffTxView v o.slot = some after → after = before.tail) := by
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
  have debit : q.dropPeeked.all = p.txQueue.all.tail := by
    have run : (p.txQueue.peek.run w).run a = .ok (((some (first :: rest),q),w),ap) := by
      simpa only [chosen] using hpeek
    have split := prev_peek_then_drop p.txQueue w w a ap (first :: rest) q run
    simp only [split,List.tail_cons]
  rw [chosen] at hr
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
  have installView : TxDisposition.txQueues installed = fun j =>
      if o.slot = j then some q else TxDisposition.txQueues w j := by
    cases hset
    funext j
    by_cases chosen : o.slot = j <;>
      simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,hd,
        Std.TreeMap.getElem?_insert,chosen]
  have nextHead : TxDisposition.HeadState first .crypted installed := by
    cases hset
    simpa [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd] using head
  obtain ⟨others,survivor⟩ := crypted_body_queues o.slot first rest nextHead ai b hr
  constructor
  · intro j ne
    rw [others j ne,logical_factor,installView,logical_factor]
    simp [Ne.symm ne]
  · intro before after hbefore hafter
    obtain ⟨old,hold,same⟩ := survivor after hafter
    rw [installView] at hold
    have oq : old = q := by simpa using hold.symm
    subst old
    have beforeEq : before = p.txQueue.all := by
      simpa [handoffTxView,hd,hp] using hbefore.symm
    subst before
    simpa only [same] using debit


/-- The actual CRYPTED head debits one logical batch and pays its supplied
owner, retaining precisely a send-only freshness delta. The selected peer may
be absent after the final put; other peers keep their complete logical queues. -/
theorem crypted_step_account (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) ∧
      (∀ other, other ≠ o.slot → handoffTxView v other = handoffTxView w other) ∧
      (∀ before after, handoffTxView w o.slot = some before →
        handoffTxView v o.slot = some after → after = before.tail) := by
  obtain ⟨resultEq,delta,noTx,funded,sends⟩ := crypted_step_send_only o first rest hi queue head a b hr
  exact ⟨resultEq,delta,noTx,funded,sends,crypted_step_queues o first rest queue head a b hr⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
