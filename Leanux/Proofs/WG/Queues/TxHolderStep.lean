import Leanux.Proofs.WG.Queues.TxHolderAccount

/-! The actual TX step either keeps its cached logical queue or consumes one
charged batch. Empty and UNCRYPTED heads do not pay a reservation; malformed
items and failed source guards retain their actual Stop behavior. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem body_classify (pid : PeerId) (selected : Option (List SkbId))
    (a b : Ambient)
    (hr : ((TxDisposition.bodySource pid selected).run w).run a = .ok ((result,v),b)) :
    (result = false ∧ v = w) ∨ ∃ first tail,
      selected = some (first :: tail) ∧
      (TxDisposition.HeadState first .dead w ∨ TxDisposition.HeadState first .crypted w) := by
  cases selected with
  | none =>
    change Except.ok ((false,w),CounterWindow.record a .txPacket false) = .ok ((result,v),b) at hr
    cases hr
    exact Or.inl ⟨rfl,rfl⟩
  | some item =>
    cases item with
    | nil =>
      change Except.error (Stop.invariant "an empty ring item") = .ok ((result,v),b) at hr
      cases hr
    | cons first tail =>
      unfold TxDisposition.bodySource at hr
      rw [MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨go,checked,ac,hgo,hr⟩ := hr
      change (((do
        let packet ← getTxSkb first
        branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
          (CounterWindow.record a .txPacket true)) = .ok ((go,checked),ac) at hgo
      rw [MaterialOrigin.bind_ok_ambient] at hgo
      obtain ⟨pkt,read,ar,hread,hbranch⟩ := hgo
      obtain ⟨readEq,_,d,hd,hp⟩ := Packets.getTxSkb_current first w read pkt _ ar hread
      subst read
      have stored : TxDisposition.txPackets w first = some pkt := by
        simp only [TxDisposition.txPackets,hd,Option.bind_some,hp]
      cases state : pkt.state with
      | uncrypted =>
        simp only [state] at hbranch
        cases hbranch
        change Except.ok ((false,w),_) = .ok ((result,v),b) at hr
        cases hr
        exact Or.inl ⟨rfl,rfl⟩
      | dead => exact Or.inr ⟨first,tail,rfl,Or.inl ⟨pkt,stored,state⟩⟩
      | crypted => exact Or.inr ⟨first,tail,rfl,Or.inr ⟨pkt,stored,state⟩⟩

private theorem peek_install {h : DurableHolders} (hi : h.Funded cs loans w)
    (stable : StableRx cs w) (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (q : PrevQueue (List SkbId)) (same : q.all = p.txQueue.all) :
    h.Funded cs loans {w with dev := some {d with peers := d.peers.insert pid {p with txQueue := q}}} ∧
    StableRx cs {w with dev := some {d with peers := d.peers.insert pid {p with txQueue := q}}} := by
  have inv := (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.queue_update)
    ⟨hi.carriers,stable⟩ hd hp q
  refine ⟨⟨hi.aligned.frame ?_,inv.1⟩,inv.2⟩
  refine ⟨?_,?_,?_⟩
  · simp only [passiveView,hd,Option.map_some]
  · simp only [sendView,hd,Option.map_some]
  · intro other batches found
    simp only [handoffTxView,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq] at found
    by_cases eq : pid = other
    · subst other
      simp only [ite_true,Option.map_some,Option.some.injEq] at found
      simpa only [handoffTxView,hd,Option.bind_some,hp,Option.map_some,same] using congrArg some found
    · simpa only [handoffTxView,hd,Option.bind_some,ite_eq_right eq] using found

private theorem step_classify {h : DurableHolders} (pid : PeerId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    (result = false ∧ h.Funded cs loans v ∧ StableRx cs v) ∨ ∃ first tail,
      (∃ batches, handoffTxView w pid = some batches ∧ batches.head? = some (first :: tail)) ∧
      (TxDisposition.HeadState first .dead w ∨ TxDisposition.HeadState first .crypted w) := by
  rw [← TxDisposition.stepSource_eq] at hr
  unfold TxDisposition.stepSource at hr
  simp only [bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d,hd,hp⟩ := getPeer_normal pid w read p a ar hread
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨⟨selected,q⟩,peeked,ap,hpeek,hr⟩ := hr
  obtain ⟨selectedEq,allEq,_,peekedEq⟩ := prev_peek_normal p.txQueue w peeked a ap selected q hpeek
  subst peeked
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d₂,hd₂,hp₂⟩ := getPeer_normal pid w read current ap ar hread
  subst read
  subst ar
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = p := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,installed,ai,hset,hr⟩ := hr
  cases u
  have installedInv : h.Funded cs loans installed ∧ StableRx cs installed := by
    cases hset
    simpa only [setPeer,modifyDev,hd,Option.map_some] using peek_install hi stable hd hp q allEq
  rcases body_classify pid selected ai b hr with idle | active
  · obtain ⟨resultEq,worldEq⟩ := idle
    exact Or.inl ⟨resultEq,worldEq ▸ installedInv⟩
  · obtain ⟨first,tail,chosen,head⟩ := active
    refine Or.inr ⟨first,tail,⟨p.txQueue.all,?_,selectedEq.symm.trans chosen⟩,?_⟩
    · simp only [handoffTxView,hd,Option.bind_some,hp,Option.map_some]
    · cases hset
      simpa only [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd,
        Option.map_some,Option.bind_some] using head

/-- Complete normal-return accounting for the actual TX step. An idle step
keeps the account; a completed step pays its actual selected batch and retains
every new send-work reservation. No readiness or head-state premise is needed. -/
theorem txStep_funded {h : DurableHolders} (pid : PeerId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    (result = false ∧ h.Funded cs loans v ∧ StableRx cs v) ∨
    (result = true ∧ ∃ chosen rest delta,
      TxSelected h.tx pid chosen rest ∧ chosen.item ≠ [] ∧ delta.tx = [] ∧
      ((h.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v) := by
  rcases step_classify pid hi stable a b run with idle | active
  · exact Or.inl idle
  · obtain ⟨first,tail,queue,head⟩ := active
    rcases head with dead | crypted
    · obtain ⟨resultEq,chosen,rest,selected,itemEq,funded,stability⟩ :=
        dead_holder_step pid first tail hi stable queue dead a b run
      refine Or.inr ⟨resultEq,chosen,rest,{},selected,?_,rfl,?_,stability⟩
      · intro empty
        rw [itemEq] at empty
        cases empty
      · simpa only [absorb,List.append_nil] using funded
    · obtain ⟨resultEq,chosen,rest,delta,selected,itemEq,noTx,funded,stability⟩ :=
        crypted_holder_step pid first tail hi stable queue crypted a b run
      refine Or.inr ⟨resultEq,chosen,rest,delta,selected,?_,noTx,funded,stability⟩
      intro empty
      rw [itemEq] at empty
      cases empty

/-- Existential account closure for callers which retain the actual source
transition but do not need to name its chosen batch. -/
theorem txStep_boundary (pid : PeerId) : Preserves (Boundary cs loans) (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b input run
  obtain ⟨h,hi,stable⟩ := input
  rcases txStep_funded pid hi stable a b run with idle | active
  · exact ⟨h,idle.2⟩
  · obtain ⟨_,chosen,rest,delta,_,_,_,funded,stability⟩ := active
    exact ⟨(h.withoutTx rest).absorb delta,funded,stability⟩

/-- The same complete normal account on the existing lifetime observer,
with arbitrary incoming history and the exact native Ambient endpoints. -/
theorem txStep_observed {h : DurableHolders} (pid : PeerId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (txStepPrefix pid) w a history).1 = .ok ((result,v),b)) :
    (result = false ∧ h.Funded cs loans v ∧ StableRx cs v) ∨
    (result = true ∧ ∃ chosen rest delta,
      TxSelected h.tx pid chosen rest ∧ chosen.item ≠ [] ∧ delta.tx = [] ∧
      ((h.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v) := by
  exact txStep_funded pid hi stable a b ((txStepPrefix_erases pid w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
