import Leanux.Proofs.WG.Queues.ConservationEffects

/-! The actual syscall certificate preserves each earlier carrier or records
its removal in the exact new journal suffix. No funding or successful errno
premise is used to obtain this source consequence. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SyscallEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open ConservationEffects

macro "syscall_tail_effect" call:ident es:ident et:ident er:ident ex:ident ea:ident ec:ident : tactic =>
  `(tactic|
    (apply checked_bind
     · apply checked_forIn
       intro c acc
       exact checked_bind (lift _) (fun _=>checked_pure (ForInStep.yield acc))
     · intro _
       apply checked_bind (lift _)
       intro _
       cases ($call)
       all_goals repeat' first
         | exact $es
         | exact $et
         | exact $er
         | exact $ex
         | exact $ea
         | exact $ec
         | exact lift _
         | exact checked_pure _
         | apply checked_bind
         | (intro)))

theorem tail (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup)
    (ed : Conserves hd.rule) (es : Conserves hs.rule) (et : Conserves ht.rule)
    (er : Conserves hr.rule) (ex : Conserves hx.rule)
    (ea : Conserves ha.rule) (ec : Conserves hc.rule) :
    Conserves (ConservationSyscall.tail call hd hs ht hr hx ha hc).rule := by
  unfold ConservationSyscall.tail
  apply checked_bind ed
  intro ret
  syscall_tail_effect call es et er ex ea ec

theorem bind_cut {action : RxHistory.Obs α} {nextAction : α→RxHistory.Obs β}
    {first : ConservationSource.Rule action} {next : ∀x,ConservationSource.Rule (nextAction x)}
    (effect : ∀x,Conserves (next x))
    (certificate : (ConservationSource.bind first next).relation cs w h result v k final) :
    ∃x u j middle,first.relation cs w h x u j middle ∧
      TrafficEffects.Conserved middle final j k := by
  rcases certificate with ⟨x,u,j,middle,front,rest⟩
  exact ⟨x,u,j,middle,front,effect x rest⟩

theorem tail_dispatch (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup)
    (es : Conserves hs.rule) (et : Conserves ht.rule)
    (er : Conserves hr.rule) (ex : Conserves hx.rule)
    (ea : Conserves ha.rule) (ec : Conserves hc.rule)
    (certificate : (ConservationSyscall.tail call hd hs ht hr hx ha hc).rule.relation cs w h result v k final) :
    ∃ret u j middle,hd.rule.relation cs w h ret u j middle ∧
      TrafficEffects.Conserved middle final j k := by
  unfold ConservationSyscall.tail at certificate
  apply bind_cut (first:=hd.rule) (certificate:=certificate)
  intro ret
  syscall_tail_effect call es et er ex ea ec

macro "syscall_entry_effect" effect:ident : tactic =>
  `(tactic|
    (unfold ConservationSyscall.entry
     repeat' first
       | exact $effect
       | exact lift _
       | exact checked_pure _
       | apply checked_bind
       | apply checked_branch
       | (intro)))

theorem entry (call : Syscall) {body : RxHistory.Obs α}
    (hb : ConservationSyscall.Checked loans body) (effect : Conserves hb.rule) :
    Conserves (ConservationSyscall.entry call hb).rule := by
  cases call
  case seccompInstall via flags filter len bad mode=>
    cases via <;> syscall_entry_effect effect
  all_goals syscall_entry_effect effect

theorem syscallWith (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : ConservationSyscall.Checked loans dispatch)
    (hs : ConservationSyscall.Checked loans sendWorkers)
    (ht : ConservationSyscall.Checked loans timers)
    (hr : ConservationSyscall.Checked loans route)
    (hx : ConservationSyscall.Checked loans xmit)
    (ha : ConservationSyscall.Checked loans advance)
    (hc : ConservationSyscall.Checked loans cleanup)
    (ed : Conserves hd.rule) (es : Conserves hs.rule) (et : Conserves ht.rule)
    (er : Conserves hr.rule) (ex : Conserves hx.rule)
    (ea : Conserves ha.rule) (ec : Conserves hc.rule) :
    Conserves (ConservationSyscall.syscallWith call hd hs ht hr hx ha hc).rule :=
  entry call _ (tail call hd hs ht hr hx ha hc ed es et er ex ea ec)

theorem dispatch (call : Syscall) : Conserves (ConservationSyscall.dispatch call).rule := by
  cases call
  all_goals first
    | exact injectDispatch _ _ _ _ _ _
    | exact flood _ _ _ _
    | exact batch _
    | exact observeDispatch
    | exact audit _

theorem syscall (call : Syscall) : Conserves (ConservationSyscall.rule call) := by
  unfold ConservationSyscall.rule ConservationSyscall.syscall
  apply checked_mpr (same := Configuration.syscallRx_factor call)
  apply syscallWith
  · exact dispatch call
  · exact deferred _
  · exact idle
  · exact audit _
  · exact deferred _
  · exact deferred _
  · exact audit _

end Leanux.Proofs.WG.Queues.RxCredits.SyscallEffects
