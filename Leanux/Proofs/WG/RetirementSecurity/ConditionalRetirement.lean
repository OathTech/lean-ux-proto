import Leanux.Proofs.WG.RetirementSecurity.DerivedZeroTimer
import Leanux.Proofs.WG.AuthenticatedEffects.TimerSelection

/-! Conditional retirement follows actual wheel selection, recorded firing,
clear work and the native last TX release. A retained packet reference may
outlive unpublication; completion is the later source disposal, not a timer
deadline alone. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

/-- Actual wheel selection supplies the resident peer; the initialized slot
carrier supplies its liveness. Both original dispatch and clear-worker runs
are explicit progress conditions. -/
theorem selected (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (d : Device) (device : w.wg.dev=some d) (bound : UInt64) (pid : PeerId)
    (entry : WheelEntry) (due : TimerWheel.nextDue d bound=some (pid,.zeroKeyMaterial,entry))
    (published : ∀p,d.peers[pid]?=some p→HasKeySlot p)
    (kind : Worker) (prior : Option UInt64)
    (fired : (timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),u))
    (p : Peer) (found : peerAt u.wg pid=some p) (b : Ambient)
    (cleared : ((runFlushedClearWork pid).run u.wg).run u.ambient=.ok (((),v),b)) :
    ZeroTimerDispatch.Queued pid u.wg ∧ HolderAccount [] v ∧ SlotsCleared pid v ∧
      (∀id∈Unpublication.SlotEntries p,Unpublished id v) ∧ Retains u.wg v := by
  obtain ⟨original,resident,_⟩ := AuthenticatedEffects.TimerSlots.due_resident d bound pid .zeroKeyMaterial entry
    (AuthenticatedEffects.TimerSlots.nextDue_member d bound pid .zeroKeyMaterial entry due)
  have foundOriginal:peerAt w.wg pid=some original:=by simp [peerAt,device,resident]
  obtain ⟨account,queued⟩ := ZeroTimerDispatch.initialized_dispatch trace placeholders initialized
    kind pid entry prior original foundOriginal (published original resident) fired
  have paid := (hoare_iff_run_ambient _ _ _).mp (flushed_holders pid []) u.wg u.ambient () v b account cleared
  have unpublished := Unpublication.flushed pid p found u.ambient b cleared
  exact ⟨queued,paid,unpublished.1,unpublished.2,(flushed_retirement pid u.wg v u.ambient b cleared).2⟩

/-- After native timer clearing, a queued TX batch may own the remaining
reference. Its actual successful worker release removes that allocation;
the holder count is read from the concrete post-clear census. -/
theorem final_tx (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (d : Device) (device : w.wg.dev=some d) (bound : UInt64) (pid : PeerId)
    (entry : WheelEntry) (due : TimerWheel.nextDue d bound=some (pid,.zeroKeyMaterial,entry))
    (published : ∀p,d.peers[pid]?=some p→HasKeySlot p)
    (kind : Worker) (prior : Option UInt64)
    (fired : (timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),u))
    (p : Peer) (found : peerAt u.wg pid=some p) (b c : Ambient)
    (cleared : ((runFlushedClearWork pid).run u.wg).run u.ambient=.ok (((),v),b))
    (allocation : Credits.Allocation) (old : allocation.slot∈Unpublication.SlotEntries p)
    (projected : durableLoans v=some loans) (last : (loans.map (·.allocation)).count allocation=1)
    (sender : PeerId) (q : Peer) (items : List SkbId) (headId : SkbId) (head : DataPacket)
    (peer : peerAt v sender=some q) (queued : q.txQueue.all.head?=some items)
    (first : items.head?=some headId) (packet : TxDisposition.txPackets v headId=some head)
    (key : head.keypair=allocation.slot)
    (released : ((txStep sender).run v).run b=.ok ((true,final),c)) :
    HolderAccount [] v ∧ SlotsCleared pid v ∧ Unpublished allocation.slot v ∧
      keyAt final allocation.slot=none := by
  have retired := selected trace placeholders initialized d device bound pid entry due published
    kind prior fired p found b cleared
  exact ⟨retired.2.1,retired.2.2.1,retired.2.2.2.1 allocation.slot old,
    FinalDisposal.tx_step allocation retired.2.1 projected last sender q items headId head
      peer queued first packet key b c released⟩

end Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
