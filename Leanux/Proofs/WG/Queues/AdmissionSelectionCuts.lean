import Leanux.Proofs.WG.Queues.SyscallSelection

/-! Introduction from independently supplied actual source cuts. The enclosing
certificate supplies the unselected continuation. These laws do not define
admission coverage by the query they prove. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionSelectionCuts
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection

theorem bind_left {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    (first : ConservationSource.Rule action) (next : ∀x,ConservationSource.Rule (nextAction x))
    (query : Query first)
    (source : (ConservationSource.bind first next).relation cs w h y v k final)
    (front : first.relation cs w h x u j middle) (chosen : query front c) :
    left first next query source c := by
  obtain ⟨x',u',j',middle',front',tail⟩ := source
  obtain ⟨rfl,rfl⟩ := (first.source front').symm.trans (first.source front)
  have same := first.unique front' front
  subst middle'
  exact ⟨x,u,j,middle,front,tail,chosen⟩

theorem bind_right {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    (first : ConservationSource.Rule action) (next : ∀x,ConservationSource.Rule (nextAction x))
    (query : ∀x,Query (next x))
    (source : (ConservationSource.bind first next).relation cs w h y v k final)
    (front : first.relation cs w h x u j middle)
    (tail : (next x).relation middle u j y v k final) (chosen : query x tail c) :
    right first next query source c := ⟨x,u,j,middle,front,tail,chosen⟩

/-- Dispatch selection uses the exact flood path position. Final membership
is not required: the selected packet may already have been removed. -/
theorem flood (count port family : Nat) (messages : List (List UInt8)) (index : Nat)
    (source : (ConservationSyscall.dispatch (.wgFlood count port family messages)).rule.relation
      cs w h result v k next)
    (selected : TrafficOccurrences.FloodAdmission cs next count port family messages w v h k result index c) :
    SyscallSelection.dispatch (.wgFlood count port family messages) index source c := selected

theorem batch (items : List Env.BatchItem) (waitMs index : Nat)
    (source : (ConservationSyscall.dispatch (.wgBatch items waitMs)).rule.relation cs w h result v k next)
    (selected : TrafficOccurrences.BatchAdmission cs next items w v h k result index c) :
    SyscallSelection.dispatch (.wgBatch items waitMs) index source c := selected

/-- A complete normally returned syscall tail provides the actual later
callbacks. The selected dispatch need only supply its own source certificate. -/
theorem tail (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup) (query : Query hd.rule)
    (source : (ConservationSyscall.tail call hd hs ht hr hx ha hc).rule.relation cs w h result v k next)
    (front : hd.rule.relation cs w h ret u j middle) (chosen : query front c) :
    SyscallSelection.tail call hd hs ht hr hx ha hc query source c := by
  unfold SyscallSelection.tail
  exact bind_left hd.rule _ query source front chosen

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionSelectionCuts
