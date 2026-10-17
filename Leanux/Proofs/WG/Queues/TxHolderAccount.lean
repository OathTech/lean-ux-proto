import Leanux.Proofs.WG.Queues.TxHolderSelection
import Leanux.Proofs.WG.Queues.TxHolderFrames
import Leanux.Proofs.WG.Queues.CryptedTxDebit

/-! Actual DEAD/CRYPTED head steps debit the ordered durable batch account,
pay its source-supplied reservation and absorb only the newly funded send work. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem aligned_tx_paid {h : DurableHolders} (hi : h.Aligned w)
    (selected : TxSelected h.tx pid chosen rest) (noTx : delta.tx = [])
    (source : handoffTxView w pid = some (h.items pid))
    (passive : passiveView v = passiveView w)
    (sends : sendView v = (sendView w).map (· ++ delta.send.map Owner.slot))
    (others : ∀ q, q ≠ pid → handoffTxView v q = handoffTxView w q)
    (debit : ∀ before after, handoffTxView w pid = some before →
      handoffTxView v pid = some after → after = before.tail) :
    ((h.withoutTx rest).absorb delta).Aligned v := by
  have list := congrArg Prod.fst passive
  have clear := congrArg (fun x => x.2.1) passive
  have cursor7 := congrArg (fun x => x.2.2.1) passive
  have cursor8 := congrArg (fun x => x.2.2.2) passive
  refine ⟨hi.base.trans list.symm,?_,hi.clear.trans clear.symm,?_,
    hi.cursor7.trans cursor7.symm,hi.cursor8.trans cursor8.symm⟩
  · intro d hd
    cases hw : w.dev with
    | none => simp [sendView,hd,hw] at sends
    | some old =>
      have eq : d.sendWorkQueue = old.sendWorkQueue ++ delta.send.map Owner.slot := by
        simpa only [sendView,hd,hw,Option.map_some,Option.some.injEq] using sends
      simpa only [absorb,withoutTx,List.map_append,hi.send old hw] using eq
  · intro q batches found
    have absorbed : ((h.withoutTx rest).absorb delta).items q = (h.withoutTx rest).items q := by
      simp [absorb,items,noTx]
    rw [absorbed]
    by_cases same : q = pid
    · subst q
      rw [debit _ batches source found,selected.head,List.tail_cons]
    · rw [selected.other q same]
      exact hi.tx q batches ((others q same) ▸ found)

private theorem funded_tx_paid {h : DurableHolders}
    (aligned : ((h.withoutTx rest).absorb delta).Aligned v)
    (funded : ClearWork.Inv cs (((h.withoutTx rest).owners ++ loans) ++ delta.owners) v) :
    ((h.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v := by
  refine ⟨⟨aligned,WorkReservations.carrier_loans_perm funded.1 ?_⟩,funded.2⟩
  apply List.perm_iff_count.mpr
  intro o
  simp only [List.count_append,absorb_count]
  omega

/-- The selected batch comes from the actual logical queue and the aligned
ordered holder list. Its existing charge pays the source step; a produced
handshake-send occurrence is retained in the lasting account. -/
theorem crypted_holder_step {h : DurableHolders} (pid : PeerId) (first : SkbId) (tail : List SkbId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (queue : ∃ batches, handoffTxView w pid = some batches ∧ batches.head? = some (first :: tail))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ chosen rest delta,
      TxSelected h.tx pid chosen rest ∧ chosen.item = first :: tail ∧ delta.tx = [] ∧
      ((h.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v := by
  obtain ⟨batches,found,firstEq⟩ := queue
  obtain ⟨chosen,rest,selected,itemEq,p,resident,headEq⟩ := hi.tx_selected found firstEq
  have input := hi.tx_input stable selected
  have native : ((txStep chosen.owner.slot).run w).run a = .ok ((result,v),b) := by
    simpa only [selected.slot] using run
  obtain ⟨resultEq,delta,noTx,funded,sends,others,debit⟩ :=
    TxReservation.crypted_step_account chosen.owner first tail input ⟨p,resident,headEq⟩ head a b native
  have passive := (ProjectedAction.iff_run_ambient _ _ _).mp (txStep_passive pid) w a result v b run
  have aligned := aligned_tx_paid hi.aligned selected noTx
    (by rw [←hi.aligned.tx pid batches found]; exact found) passive sends
    (by simpa only [selected.slot] using others) (by simpa only [selected.slot] using debit)
  exact ⟨resultEq,chosen,rest,delta,selected,itemEq,noTx,funded_tx_paid aligned funded⟩


/-- The DEAD path pays its selected batch without adding any lasting holder. -/
theorem dead_holder_step {h : DurableHolders} (pid : PeerId) (first : SkbId) (tail : List SkbId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (queue : ∃ batches, handoffTxView w pid = some batches ∧ batches.head? = some (first :: tail))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ chosen rest,
      TxSelected h.tx pid chosen rest ∧ chosen.item = first :: tail ∧
      (h.withoutTx rest).Funded cs loans v ∧ StableRx cs v := by
  obtain ⟨batches,found,firstEq⟩ := queue
  obtain ⟨chosen,rest,selected,itemEq,p,resident,headEq⟩ := hi.tx_selected found firstEq
  have input := hi.tx_input stable selected
  have native : ((txStep chosen.owner.slot).run w).run a = .ok ((result,v),b) := by
    simpa only [selected.slot] using run
  obtain ⟨resultEq,funded,_,_,others,debit⟩ :=
    TxReservation.dead_step_account chosen.owner first tail input ⟨p,resident,headEq⟩ head a b native
  have passive := (ProjectedAction.iff_run_ambient _ _ _).mp (txStep_passive pid) w a result v b run
  have sends := dead_step_send chosen.owner first tail ⟨p,resident,headEq⟩ head a b native
  have logical (u : WGWorld) (q : PeerId) :
      handoffTxView u q = (TxDisposition.txQueues u q).map (·.all) := by
    simp [handoffTxView,TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,Option.map_map,Function.comp_def]
  have logicalOthers : ∀ q, q ≠ pid → handoffTxView v q = handoffTxView w q := by
    intro q ne
    rw [logical,logical,others q (by simpa only [selected.slot] using ne)]
  have logicalDebit : ∀ before after, handoffTxView w pid = some before →
      handoffTxView v pid = some after → after = before.tail := by
    intro before after hb ha
    rw [logical] at hb ha
    cases hw : TxDisposition.txQueues w pid with
    | none => simp [hw] at hb
    | some old =>
      cases hv : TxDisposition.txQueues v pid with
      | none => simp [hv] at ha
      | some current =>
        have beforeEq : old.all = before := by simpa [hw] using hb
        have afterEq : current.all = after := by simpa [hv] using ha
        rw [←beforeEq,←afterEq]
        exact debit old current (by simpa only [selected.slot] using hw) (by simpa only [selected.slot] using hv)
  have aligned := aligned_tx_paid (delta := {}) hi.aligned selected rfl
    (by rw [←hi.aligned.tx pid batches found]; exact found) passive
    (by simpa using sends) logicalOthers logicalDebit
  have aligned' : (h.withoutTx rest).Aligned v := by simpa [absorb] using aligned
  exact ⟨resultEq,chosen,rest,selected,itemEq,⟨aligned',funded.1⟩,funded.2⟩

/-- The existing lifetime observer retains the identical normal endpoint
and the complete durable account, for arbitrary incoming journal. -/
theorem crypted_holder_observed {h : DurableHolders} (pid : PeerId) (first : SkbId) (tail : List SkbId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (queue : ∃ batches, handoffTxView w pid = some batches ∧ batches.head? = some (first :: tail))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient) (history : List LifetimeEvent)
    (run : (runStatePrefix (txStepPrefix pid) w a history).1 = .ok ((result,v),b)) :
    result = true ∧ ∃ chosen rest delta,
      TxSelected h.tx pid chosen rest ∧ chosen.item = first :: tail ∧ delta.tx = [] ∧
      ((h.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v := by
  exact crypted_holder_step pid first tail hi stable queue head a b
    ((txStepPrefix_erases pid w a history).symm.trans run)

theorem dead_holder_observed {h : DurableHolders} (pid : PeerId) (first : SkbId) (tail : List SkbId)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (queue : ∃ batches, handoffTxView w pid = some batches ∧ batches.head? = some (first :: tail))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient) (history : List LifetimeEvent)
    (run : (runStatePrefix (txStepPrefix pid) w a history).1 = .ok ((result,v),b)) :
    result = true ∧ ∃ chosen rest,
      TxSelected h.tx pid chosen rest ∧ chosen.item = first :: tail ∧
      (h.withoutTx rest).Funded cs loans v ∧ StableRx cs v := by
  exact dead_holder_step pid first tail hi stable queue head a b
    ((txStepPrefix_erases pid w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
