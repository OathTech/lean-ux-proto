import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextCompletion

/-! Physical queue ownership identifies every batch sharing a selected
packet. Thus native CRYPTED publication establishes completion for precisely
its peer-owned batch and leaves all other ready batches intact. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
variable {id : SkbId}

theorem flattened_same (batches : List (List Nat)) (unique : batches.flatten.Nodup)
    (left : a∈batches) (right : b∈batches) (shared : id∈a) (also : id∈b) : a=b := by
  induction batches with
  | nil=>simp at left
  | cons batch rest ih=>
    have parts:=List.nodup_append.mp unique
    rcases List.mem_cons.mp left with rfl | leftTail
    · rcases List.mem_cons.mp right with rfl | rightTail
      · rfl
      · exact False.elim (parts.2.2 id shared id (List.mem_flatten.mpr ⟨b,rightTail,also⟩) rfl)
    · rcases List.mem_cons.mp right with rfl | rightTail
      · exact False.elim (parts.2.2 id also id (List.mem_flatten.mpr ⟨a,leftTail,shared⟩) rfl)
      · exact ih parts.2.1 leftTail rightTail

theorem shared_batch (physical : TxInventory locals w)
    (left : TxQueuedBatch w a) (right : TxQueuedBatch w b)
    (shared : id∈a) (also : id∈b) : a=b := by
  obtain ⟨pid,p,found,queued⟩:=left
  obtain ⟨other,q,resident,member⟩:=right
  by_cases same:pid=other
  · subst other
    have eq:p=q:=Option.some.inj (found.symm.trans resident)
    subst q
    exact flattened_same p.txQueue.all (physical.queueUnique pid p found) queued member shared also
  · exact False.elim (physical.peersSeparate pid p other q found resident same id
      (List.mem_flatten.mpr ⟨a,queued,shared⟩) (List.mem_flatten.mpr ⟨b,member,also⟩))

/-- The real selected encryption continuation preserves readiness coherence.
Its input physical inventory is the same derived inventory used by the shared
driver's poll cuts, rather than an assumption that ready bytes already exist. -/
theorem native_tail_preserves (items : List SkbId)
    (physical : OccurrenceStack.Ready locals (items::active) w.wg) (before : Inv w.wg)
    (run : (RxWorkers.encryptStepTailSource (some items)).run w=.ok (result,v)) : Inv v.wg := by
  have queues:TxDisposition.txQueues v.wg=TxDisposition.txQueues w.wg:=congrArg Prod.snd ((ProjectedAction.iff_run _ _ _).mp
    (encrypt_tail_context (some items)) w result v run)
  have selected:=physical.2.2.selected_owned
  intro pid p found batch member first head crypted
  have finalQueue:TxDisposition.txQueues v.wg pid=some p.txQueue:=by
    simpa only [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,peerAt,Option.map_some] using
      congrArg (Option.map (·.txQueue)) found
  rw [queues] at finalQueue
  obtain ⟨old,resident,queue⟩:=Option.map_eq_some_iff.mp finalQueue
  have owned:TxQueuedBatch w.wg batch:=⟨pid,old,resident,queue.symm ▸ member⟩
  by_cases same:batch=items
  · subst batch
    exact native_tail items first head run crypted
  · have outside:∀id∈batch,id∉items:=by
      intro id inside overlap
      exact same (shared_batch physical.2.1 owned selected inside overlap)
    have firstOutside:=outside first (List.mem_of_head? head)
    have headSame:TxDisposition.txPackets v.wg first=TxDisposition.txPackets w.wg first:=
      (ProjectedAction.iff_run _ _ _).mp (TxDisposition.SelectedEncrypt.step_other first items firstOutside)
        w result v run
    have oldHead:TxDisposition.HeadState first .crypted w.wg:=by
      obtain ⟨packet,stored,mark⟩:=crypted
      exact ⟨packet,headSame ▸ stored,mark⟩
    have complete:=before pid old resident batch (queue.symm ▸ member) first head oldHead
    intro id inside
    apply (complete id inside).frame
    exact (ProjectedAction.iff_run _ _ _).mp (TxDisposition.SelectedEncrypt.step_other id items (outside id inside))
      w result v run

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
