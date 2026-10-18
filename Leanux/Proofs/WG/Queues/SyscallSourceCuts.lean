import Leanux.Proofs.WG.Queues.SyscallEntryCuts

/-! Every normally returned traffic syscall exposes its actual entry and
dispatch source cuts before an admission is selected. The existing source
certificate supplies all later callbacks, including normal errno tails. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SyscallSourceCuts
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection

/-- Reindexing retains the same source certificate and every query on it. -/
theorem mpr_cut {action other : RxHistory.Obs α}
    (same : action=other)
    (types : ConservationSyscall.Checked loans action=ConservationSyscall.Checked loans other)
    (checked : ConservationSyscall.Checked loans other)
    (source : (Eq.mpr types checked).rule.relation cs w h result v k next) :
    ∃certificate : checked.rule.relation cs w h result v k next,
      ∀query : Query checked.rule,∀c,query certificate c→
        SyscallSelection.mpr same types checked query source c := by
  cases same
  exact ⟨source,fun _ _ selected=>selected⟩

/-- Entry resets and its actual seccomp guard are retained at the cut. -/
theorem entry_cut (call : Syscall) (traffic : SyscallEntryCuts.TrafficCall call)
    {body : RxHistory.Obs α} (checked : ConservationSyscall.Checked loans body)
    (source : (ConservationSyscall.entry call checked).rule.relation cs w h result v k next) :
    ∃u,runPrefix (SyscallEntryCuts.enter call) w h=(.ok ((),u),h) ∧
      ∃certificate : checked.rule.relation cs u h result v k next,
        ∀query : Query checked.rule,∀c,query certificate c→
          SyscallSelection.entry call checked query source c := by
  obtain ⟨u,entered,certificate⟩ := SyscallEntryCuts.traffic_body call traffic checked source
  exact ⟨u,entered,certificate,fun query c selected=>
    SyscallEntryCuts.traffic_selected_at call traffic checked query source entered certificate selected⟩

/-- The actual dispatch return precedes every return-to-user callback. -/
theorem tail_cut (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup)
    (source : (ConservationSyscall.tail call hd hs ht hr hx ha hc).rule.relation cs w h result v k next) :
    ∃ret u j middle,∃certificate : hd.rule.relation cs w h ret u j middle,
      ∀query : Query hd.rule,∀c,query certificate c→
        SyscallSelection.tail call hd hs ht hr hx ha hc query source c := by
  obtain ⟨ret,u,j,middle,front,rest⟩ := source
  exact ⟨ret,u,j,middle,front,fun query c selected=>
    AdmissionSelectionCuts.tail call hd hs ht hr hx ha hc query
      ⟨ret,u,j,middle,front,rest⟩ front selected⟩

/-- A traffic syscall's actual dispatch certificate is exposed without
choosing any packet; every dispatch query then lifts to the complete syscall. -/
theorem syscall_cut (call : Syscall) (traffic : SyscallEntryCuts.TrafficCall call)
    (source : (ConservationSyscall.rule call).relation cs w h result v k next) :
    ∃entered ret returned received admitted,
      runPrefix (SyscallEntryCuts.enter call) w h=(.ok ((),entered),h) ∧
      ∃front : (ConservationSyscall.dispatch call).rule.relation
        cs entered h ret returned received admitted,
        ∀inner c,SyscallSelection.dispatch call inner front c→
          SyscallSelection.syscall call inner source c := by
  unfold ConservationSyscall.rule ConservationSyscall.syscall at source
  obtain ⟨body,liftBody⟩ := mpr_cut (Configuration.syscallRx_factor call) _ _ source
  obtain ⟨entered,start,tail,liftTail⟩ := entry_cut call traffic _ body
  obtain ⟨ret,returned,received,admitted,front,liftFront⟩ := tail_cut call _ _ _ _ _ _ _ tail
  refine ⟨entered,ret,returned,received,admitted,start,front,?_⟩
  intro inner c selected
  exact liftBody _ c (liftTail _ c (liftFront _ c selected))

end Leanux.Proofs.WG.Queues.RxCredits.SyscallSourceCuts
