import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastFrames

/-! A completed native worker removes its selected alias and protects every
new encryption identity against all remaining pending batches. The stopped
prefix still has no repeated identity. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

private theorem remove_active (before : Protected label (items :: active) s) :
    Protected label active s := by
  apply before.shrink (Nat.le_refl _)
  intro d found
  refine ⟨d,found,rfl,Nat.le_refl _,?_⟩
  intro id member
  obtain ⟨batch,queued,inside⟩ := List.mem_flatten.mp member
  apply List.mem_flatten.mpr
  refine ⟨batch,?_,inside⟩
  rcases List.mem_append.mp queued with ring | remaining
  · exact List.mem_append_left _ ring
  · exact List.mem_append_right _ (List.mem_cons_of_mem items remaining)

theorem selected_protected {id : SkbId} (physical : OccurrenceStack.Ready [] (items :: active) w)
    (member : id ∈ items) : Protected (PacketOrigins.epoch w,id) active (view w) := by
  obtain ⟨packet,resident⟩ := physical.2.2.selected_resident physical.2.1 id member
  obtain ⟨history,allocated⟩ := physical.1
  cases device : w.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    have stored : d.txSkbs[id]? = some packet := by
      simpa only [TxDisposition.txPackets,device,Option.bind_some] using resident
    have bound : id + 1 ≤ d.nextSkb :=
      allocated.packetBounded d device (.inl id) (id + 1) (by
        simp only [Packets.deviceStore,stored,Option.map_some])
    refine ⟨d.ifindex,by simp [PacketOrigins.epoch,device],allocated.epochBounded d device,?_⟩
    intro current found same
    have equal : current = ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩ := by
      simpa only [view,device,Option.map_some,Option.some.injEq] using found.symm
    subst current
    refine ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self id) bound,?_⟩
    simpa only [txCryptItems,device,Option.map_some,Option.getD_some] using
      physical.2.2.selected_disjoint id member

/-- On return the selected alias is gone and every old or newly encrypted
identity is excluded from every pending alias. On Stop only the journal's
non-repetition assertion is made, because the native monad has no output world. -/
theorem worker (physical : OccurrenceStack.Ready [] (items :: active) w.wg)
    (past : Inv (h.map WorkerEpochs.identity) (items :: active) (view w.wg)) :
    let execution := runPrefix (WorkerEncryption.tail (some items)) w h
    (execution.2.map WorkerEpochs.identity).Nodup ∧
      ∀ result v, execution.1 = .ok (result,v) →
        Inv (execution.2.map WorkerEpochs.identity) active (view v.wg) := by
  have unique := worker_nonreuse physical past
  refine ⟨unique,?_⟩
  intro result v run
  have native : (RxWorkers.encryptStepTailSource (some items)).run w = .ok (result,v) :=
    (WorkerEncryption.tail_erases (some items) w h).symm.trans run
  have same := (ProjectedAction.iff_run _ _ _).mp (native_tail (some items)) w result v native
  rw [same]
  refine ⟨unique,?_⟩
  intro label member
  obtain ⟨suffix,extension,sub,epochs⟩ := WorkerEpochs.tail_suffix (some items) w h
  rw [extension,List.map_append] at member
  rcases List.mem_append.mp member with old | fresh
  · exact remove_active (past.2 label old)
  · obtain ⟨receipt,inside,rfl⟩ := List.mem_map.mp fresh
    have selected : receipt.id ∈ items := sub.subset (List.mem_map.mpr ⟨receipt,inside,rfl⟩)
    have equal : WorkerEpochs.identity receipt = (PacketOrigins.epoch w.wg,receipt.id) :=
      Prod.ext (epochs receipt inside) rfl
    rw [equal]
    exact selected_protected physical selected

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
