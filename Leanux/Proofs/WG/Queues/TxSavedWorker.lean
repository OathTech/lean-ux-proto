import Leanux.Proofs.WG.Queues.TxRxHeadNapi
import Leanux.Proofs.WG.Queues.TxLogicalSelection

/-! Exact adjacent source cuts: fresh full-ring refusal, original encryption
selection, actual softirq, and the saved-item encryption continuation. R2
allocation validity is supplied at the worker entry, before its ring poll. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.SavedWorker
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem poll_allocation (hi : AllocationInv history w.wg)
    (run : (liftWG TxRing.pollSource).run w=.ok (item,v)) :
    ∃ h,AllocationInv h v.wg := by
  have keep := (pinned_const _private.Leanux.Proofs.WG.Queues.RxWorkerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptPoll_allocation)
    w history hi
  have erase := (liftWGObserver_erases (erasesStatePrefix_lift TxRing.pollSource)) w history
  have actual := erase.trans run
  change (runPrefix (liftWGObserver (liftWGPrefix TxRing.pollSource)) w history).1=.ok (item,v) at actual
  have post := keep.choose_spec.2.2
  rw [actual] at post
  exact ⟨_,post⟩

private theorem empty_tail (target : SkbId) (state : PacketState) :
    Preserves (fun w : World=>HeadState target state w.wg) (RxWorkers.encryptTailSource none) := by
  unfold RxWorkers.encryptTailSource workerIter RxWorkers.encryptStepTailSource
  simp only [Option.isSome_none,bind_assoc,pure_bind]
  exact preserves_bind
    (productAmbient_spec (AmbientM.branch .encWorkerConsumed false) _ (fun _ _ hi=>hi))
    (fun _=>preserves_pure _)

/-- This internal cut consumes the actual ring and then executes the concrete
callback. Exclusion concerns the entry's live logical items, never stale slots. -/
private theorem worker (target : SkbId) (state : PacketState)
    (allocation : AllocationInv history w.wg) (head : HeadState target state w.wg)
    (cell : TxRing.nativeCell w.wg=some (epoch,ring))
    (physical : TxRing.Refines (PtrRing.init n) ringHistory ring)
    (outside : ∀old∈ring.items,target∉old)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w=
      .ok (result,v)) : HeadState target state v.wg := by
  rw [RxWorkers.encrypt_source] at run
  obtain ⟨item,polled,poll,tail⟩ := RxCredits.bind_ok run
  obtain ⟨tick,afterIrq,irq,encrypted⟩ := RxCredits.bind_ok tail
  cases tick
  have nativePoll := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    TxRing.pollSource w polled item poll
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp
    (pinned_const _private.Leanux.Proofs.WG.Queues.TxLogicalSelection.«0».Leanux.Proofs.WG.Queues.TxDisposition.LogicalSelection.poll_packets)
    w.wg w.ambient item polled.wg polled.ambient nativePoll
  have oldHead : HeadState target state polled.wg := by
    simpa only [HeadState,cells] using head
  have valid := poll_allocation allocation poll
  have after := (hoare_iff_run _ _ _).mp (RxHeadNapi.softirq target state)
    polled () afterIrq ⟨valid,oldHead⟩ irq
  cases item with
  | none=>
    exact (hoare_iff_run _ _ _).mp (empty_tail target state) afterIrq result v after.2 encrypted
  | some selected=>
    have separated := LogicalSelection.selected_outside cell physical outside nativePoll
    exact (hoare_iff_run _ _ _).mp (SelectedEncrypt.tail_head target selected separated state)
      afterIrq result v after.2 encrypted

/-- Full-ring createData refusal followed by the actual entire encryption
iteration leaves the fresh refused head DEAD. Its selected item's exclusion is
derived from the allocator and the original live ring. The R2 allocation
witness is explicitly at the worker entry after the recorded create cut. -/
theorem refusal_encrypt (pid : PeerId) (packets : List DataPacket)
    (device : before.dev=some d) (peer : d.peers[pid]?=some p)
    (live : p.isDead=false) (room : p.txQueue.count<MAX_QUEUED_PACKETS)
    (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (physical : TxRing.Refines (PtrRing.init n) ringHistory d.encryptQueue)
    (created : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run before).run ambient=
      .ok ((first::rest,w.wg),w.ambient))
    (allocation : AllocationInv history w.wg)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w=
      .ok (result,v)) : HeadState first .dead v.wg := by
  obtain ⟨_,head,ring,apart⟩ := LogicalSelection.allocated_refusal pid packets
    device peer live room full bounded created
  exact worker first .dead allocation head ring physical apart run

/-- The unchanged persistent observer executes the same entire worker for any
incoming history. This statement uses only its actual normal source endpoint. -/
theorem refusal_observed (pid : PeerId) (packets : List DataPacket)
    (device : before.dev=some d) (peer : d.peers[pid]?=some p)
    (live : p.isDead=false) (room : p.txQueue.count<MAX_QUEUED_PACKETS)
    (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (physical : TxRing.Refines (PtrRing.init n) ringHistory d.encryptQueue)
    (created : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run before).run ambient=
      .ok ((first::rest,w.wg),w.ambient))
    (allocation : AllocationInv allocationHistory w.wg)
    (run : runPrefix RxHistory.encryptIteration w history=(.ok (result,v),after)) :
    HeadState first .dead v.wg :=
  refusal_encrypt pid packets device peer live room full bounded physical created allocation
    ((RxHistory.encryptIteration_erases w history).symm.trans (congrArg Prod.fst run))

private theorem create_allocation (pid : PeerId) (packets : List DataPacket) :
    Preserves (fun w=>∃h,AllocationInv h w)
      (do let item←packets.mapM newTxSkb;createData pid item;pure item) := by
  apply preserves_bind
  · apply mapM_view_spec id (fun w=>∃h,AllocationInv h w)
    intro packet
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.observed_allocation)
      (PacketAllocation.tx packet).observed _ (PacketAllocation.erases (.tx packet))
      (PacketAllocation.preserves (.tx packet))
  · intro item
    apply preserves_bind
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.observed_allocation)
        (createDataPrefix pid item) _ (createDataPrefix_erases pid item)
        (createDataPrefix_preserves_ambient allocationAmbient allocationTx pid item)
    · intro _
      exact preserves_pure item

/-- Allocation validity is supplied before the fresh allocation/create cut and
transported by the existing R2 source observers. All later invariant facts and
the selected item's exclusion are derived from these two adjacent actual runs. -/
theorem refusal_entry (pid : PeerId) (packets : List DataPacket)
    (device : before.dev=some d) (peer : d.peers[pid]?=some p)
    (live : p.isDead=false) (room : p.txQueue.count<MAX_QUEUED_PACKETS)
    (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (physical : TxRing.Refines (PtrRing.init n) ringHistory d.encryptQueue)
    (allocation : AllocationInv history before)
    (created : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run before).run ambient=
      .ok ((first::rest,w.wg),w.ambient))
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w=
      .ok (result,v)) : HeadState first .dead v.wg := by
  obtain ⟨later,valid⟩ := (hoare_iff_run_ambient _ _ _).mp (create_allocation pid packets)
    before ambient (first::rest) w.wg w.ambient ⟨history,allocation⟩ created
  exact refusal_encrypt pid packets device peer live room full bounded physical created valid run

theorem refusal_entry_observed (pid : PeerId) (packets : List DataPacket)
    (device : before.dev=some d) (peer : d.peers[pid]?=some p)
    (live : p.isDead=false) (room : p.txQueue.count<MAX_QUEUED_PACKETS)
    (full : d.encryptQueue.full=true)
    (bounded : ∀old∈d.encryptQueue.items,∀id∈old,id<d.nextSkb)
    (physical : TxRing.Refines (PtrRing.init n) ringHistory d.encryptQueue)
    (allocation : AllocationInv allocationHistory before)
    (created : (((do let item←packets.mapM newTxSkb;createData pid item;pure item) : WG.M (List SkbId)).run before).run ambient=
      .ok ((first::rest,w.wg),w.ambient))
    (run : runPrefix RxHistory.encryptIteration w history=(.ok (result,v),after)) :
    HeadState first .dead v.wg :=
  refusal_entry pid packets device peer live room full bounded physical allocation created
    ((RxHistory.encryptIteration_erases w history).symm.trans (congrArg Prod.fst run))

end Leanux.Proofs.WG.Queues.TxDisposition.SavedWorker
