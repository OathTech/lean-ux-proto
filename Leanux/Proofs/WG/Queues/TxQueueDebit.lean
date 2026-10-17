import Leanux.Proofs.WG.Queues.DeadTxReservation

/-! The actual TX disposal retains all surviving logical queues. Its final
peer payment may erase only the selected peer; a DEAD worker step removes one
logical batch before that payment, including a cached peek. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem peerPut_queues (pid : PeerId) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (a b : Ambient)
    (hr : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    TxDisposition.txQueues v = TxDisposition.txQueues (paymentState w d pid p) := by
  have positive := (peerPut_effect pid w v d p a b hd hp hr).1
  have nonzero : p.refcount ≠ 0 := by omega
  have hl (x : IndexM Unit) : (liftM x : WG.M Unit) = liftIndex x := rfl
  by_cases final : p.refcount = 1
  all_goals
    simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
      refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
      hl,liftIndex_run,retirePeerUnits,modifyAmbient,
      CounterWindow.branch_run,CounterWindow.branchCmp_run,
      hd,hp,positive,nonzero,final,
      StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      CounterWindow.except_ok_bind,CounterWindow.except_pure,
      invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at hr
  all_goals repeat' first | split at hr | contradiction
  all_goals rcases hr with ⟨rfl,rfl⟩
  all_goals
    funext q
    by_cases chosen : pid = q
    all_goals
    simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,paymentState,
      final,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,chosen]

private theorem freeList_queues (item : List SkbId) :
    SameView TxDisposition.txQueues (TxDisposition.freeList item) := by
  have leaf (id : SkbId) : SameView TxDisposition.txQueues (freeTxSkb id) := by
    intro initial
    unfold freeTxSkb
    apply hoare_liftSkb
    intro w d store hi hd
    change TxDisposition.txQueues _ = initial at hi ⊢
    unfold TxDisposition.txQueues PeerBorrow.resident wgStoreView at hi ⊢
    simpa only [hd,Option.bind_some] using hi
  induction item with
  | nil => simpa only [TxDisposition.freeList_nil] using SameView.pure TxDisposition.txQueues ()
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons]
    exact (leaf id).bind fun _ => ih

private theorem keyPut_queues (key : KeypairId) :
    SameView TxDisposition.txQueues (keypairPut (some key) false) := by
  intro initial
  let P := fun w => TxDisposition.txQueues w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) : Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table h hd
    change TxDisposition.txQueues _ = initial at h ⊢
    unfold TxDisposition.txQueues PeerBorrow.resident wgStoreView at h ⊢
    simpa only [hd,Option.bind_some] using h
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    change TxDisposition.txQueues _ = initial at hi ⊢
    unfold TxDisposition.txQueues PeerBorrow.resident wgStoreView at hi ⊢
    simpa [Option.bind_map,Function.comp_def,hf] using hi
  change Preserves P _
  unfold keypairPut getKeypair getDev setKeypair
  simp only [branch,branchCmp,refcountDecAndTest,invariant,unsupported]
  repeat' first
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals exact read

/-- Disposal changes no other peer's complete TX queue. Any surviving
selected peer retains its queue as well; final erasure is not forbidden. -/
theorem dispose_queues (pid : PeerId) (item : List SkbId) (key : KeypairId)
    (a b : Ambient)
    (hr : ((TxDisposition.disposeSource pid item key).run w).run a = .ok ((result,v),b)) :
    (∀ other, other ≠ pid → TxDisposition.txQueues v other = TxDisposition.txQueues w other) ∧
      (∀ q, TxDisposition.txQueues v pid = some q → TxDisposition.txQueues w pid = some q) := by
  have factor : TxDisposition.disposeSource pid item key = (do
    TxDisposition.freeList item
    keypairPut (some key) false
    peerPut (some pid)
    pure true : WG.M Bool) := by
    simp only [TxDisposition.disposeSource,TxDisposition.freeList,bind_assoc,pure_bind]
  rw [factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,freed,af,hfree,hr⟩ := hr
  cases u
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp (freeList_queues item) w a () freed af hfree
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,keys,ak,hkey,hr⟩ := hr
  cases u
  have hk := (ProjectedAction.iff_run_ambient _ _ _).mp (keyPut_queues key) freed af () keys ak hkey
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,paid,ap,hpay,hr⟩ := hr
  cases u
  obtain ⟨d,p,hd,hp⟩ : ∃ d p, keys.dev = some d ∧ d.peers[pid]? = some p := by
    cases hd : keys.dev with
    | none =>
      simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
        getPeer,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind,
        StateT.run_monadLift,CounterWindow.except_ok_bind] at hpay
      cases hpay
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
          getPeer,getDev,hd,hp,invariant,AmbientM.invariant,StateT.run_bind,
          StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind] at hpay
        cases hpay
      | some p => exact ⟨d,p,rfl,hp⟩
  have hq := peerPut_queues pid hd hp ak ap hpay
  have prior := hk.trans hf
  have others : ∀ other, other ≠ pid → TxDisposition.txQueues paid other = TxDisposition.txQueues w other := by
    intro other ne
    rw [hq,← prior]
    by_cases final : p.refcount = 1 <;>
      simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,paymentState,hd,
        final,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,Ne.symm ne]
  have survivor : ∀ q, TxDisposition.txQueues paid pid = some q → TxDisposition.txQueues w pid = some q := by
    intro q h
    rw [hq] at h
    by_cases final : p.refcount = 1
    · simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,paymentState,final] at h
    · rw [← prior]
      simpa [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,paymentState,hd,hp,final] using h
  cases hr
  exact ⟨others,survivor⟩

/-- The DEAD body performs the literal dropPeeked before disposal. The
selected peer may disappear, but every surviving queue has the exact source
debit and all other peers retain their complete queue representation. -/
theorem dead_body_queues (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource pid (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) :
    (∀ other, other ≠ pid → TxDisposition.txQueues v other = TxDisposition.txQueues w other) ∧
      (∀ q, TxDisposition.txQueues v pid = some q →
        ∃ old, TxDisposition.txQueues w pid = some old ∧ q = old.dropPeeked) := by
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
    obtain ⟨readEq,dead⟩ :=
      (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.dead_read)
        head _ _ hread
    subst readWorld
    simp only [dead] at hbranch
    cases hbranch
    exact ⟨rfl,rfl⟩
  obtain ⟨goEq,checkedEq⟩ := hg
  subst go
  subst checked
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,List.head?_cons,bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,readWorld,ar,hread,hr⟩ := hr
  obtain ⟨readEq,dead⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.dead_read)
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
  have dropView : TxDisposition.txQueues dropped = fun q =>
      if pid = q then some saved.txQueue.dropPeeked else TxDisposition.txQueues w q := by
    cases hdrop
    funext q
    by_cases chosen : pid = q <;>
      simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,hd,
        Std.TreeMap.getElem?_insert,chosen]
  simp only [dead] at hr
  change ((TxDisposition.disposeSource pid (first :: rest) pkt.keypair).run dropped).run
      (CounterWindow.record ad .txCrypted false) = .ok ((result,v),b) at hr
  obtain ⟨others,survivor⟩ := dispose_queues pid (first :: rest) pkt.keypair _ b hr
  constructor
  · intro q ne
    rw [others q ne,dropView]
    simp [Ne.symm ne]
  · intro q hq
    have droppedQueue := survivor q hq
    rw [dropView] at droppedQueue
    have same : q = saved.txQueue.dropPeeked := by simpa using droppedQueue.symm
    exact ⟨saved.txQueue,by simp [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,hd,hp],same⟩

/-- One actual DEAD step removes the first logical batch, whether initially
cached or not. Only the selected peer may be erased by the final payment. -/
theorem dead_step_queues (o : Owner) (first : SkbId) (rest : List SkbId)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    (∀ other, other ≠ o.slot → TxDisposition.txQueues v other = TxDisposition.txQueues w other) ∧
      (∀ before after, TxDisposition.txQueues w o.slot = some before →
        TxDisposition.txQueues v o.slot = some after → after.all = before.all.tail) := by
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
  have nextHead : TxDisposition.HeadState first .dead installed := by
    cases hset
    simpa [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd] using head
  obtain ⟨others,survivor⟩ := dead_body_queues o.slot first rest nextHead ai b hr
  constructor
  · intro j ne
    rw [others j ne,installView]
    simp [Ne.symm ne]
  · intro before after hbefore hafter
    obtain ⟨old,hold,same⟩ := survivor after hafter
    rw [installView] at hold
    have oq : old = q := by simpa using hold.symm
    subst old
    have beforeEq : before = p.txQueue := by
      simpa [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,hd,hp] using hbefore.symm
    subst before
    simpa only [same] using debit

/-- The same actual DEAD-step receipt joins exact queue debit and funded
payment, without assuming the selected peer survives or adding spare credit. -/
theorem dead_step_account (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v ∧
      (∀ id ∈ first :: rest, TxDisposition.txPackets v id = none) ∧ v.sent = w.sent ∧
      (∀ other, other ≠ o.slot → TxDisposition.txQueues v other = TxDisposition.txQueues w other) ∧
      (∀ before after, TxDisposition.txQueues w o.slot = some before →
        TxDisposition.txQueues v o.slot = some after → after.all = before.all.tail) := by
  have paid := dead_step_endpoint o first rest hi queue head a b hr
  have debit := dead_step_queues o first rest queue head a b hr
  exact ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2,debit⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
