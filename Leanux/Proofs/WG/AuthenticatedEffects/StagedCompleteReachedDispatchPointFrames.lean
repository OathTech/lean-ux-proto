import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointCanonical

/-! Concrete native projection frames and actual child normal endpoints. The
child deletion arm alone keeps the source's stronger Ready/DeleteEntry input;
no generic packet Carrier is promoted to that companion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 800000

def Family.Entry (family : Family) (h : History) (w : World) : Prop :=
  match family with
  | .delete => Runner.Points.Child.Entry (.dispatch .wgDelete) h w
  | _ => CompleteProduct.Carrier h w

def Child.Entry : {α : Type} → {action : PrefixM Event α} → Child action → History → World → Prop
  | _,_,.family source => source.Entry

theorem Child.entry_carrier (child : Child action) (before : child.Entry h w) : CompleteProduct.Carrier h w := by
  cases child with
  | family family => cases family <;> first | exact before | exact before.1.1

theorem Native.checked (token : Native action) : CompleteProduct.Checked (liftPrefix action) := by
  cases token with
  | stored source => exact source.checked
  | fs body => exact CompleteProduct.fs body
  | seccomp body => exact CompleteProduct.seccomp body
  | ambient body => exact CompleteProduct.ambient body
  | ambientEdit f => exact CompleteProduct.ambient (modify f)
  | read => exact CompleteProduct.read
  | files => exact CompleteProduct.fs (getFiles : FS.M FilesStruct)
  | task ref => exact CompleteProduct.fs (monadLift (TaskM.getTask ref) : FS.M Task)
  | nextFile id => exact CompleteProduct.edit _ (fun _=>rfl)
  | modifyFiles f => exact CompleteProduct.fs (monadLift (TaskM.modifyTask .task (fun t=>{t with files:=f t.files})) : FS.M Unit)
  | control c =>
    have kept : DispatchRetained c.call := by cases c <;> trivial
    have checked := CompleteProduct.Administrative.retained c.call kept
    cases c <;> exact checked
  | observeFront => exact CompleteProduct.product_store _ DeliverySource.observeFront_store
  | observeFinish => exact CompleteProduct.product_store _ DeliverySource.observeFinish_store
  | nlRead fd => exact CompleteProduct.wg _ (CompleteDump.native _ ((getNlSock_sameWGWorld fd).factor dumpView))
  | nlWrite fd sock => exact CompleteProduct.wg _ (CompleteDump.native _ (setNlSock_sameDump fd sock))

theorem Native.normal (token : Native action) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (liftPrefix action) w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
  obtain ⟨_,_,_,post⟩ := token.checked w h before
  simpa only [performed] using post

theorem Family.normal (family : Family) {value : family.Result} (before : family.Entry h w)
    (performed : runPrefix family.action w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
  have use {α : Type} {body : PrefixM Event α} (checked : CompleteProduct.Checked body)
      {out : α} (before : CompleteProduct.Carrier h w) (run : runPrefix body w h=(.ok (out,v),last)) :
      CompleteProduct.Carrier last v := by
    obtain ⟨_,_,_,post⟩ := checked w h before
    simpa only [run] using post
  cases family with
  | config attrs => exact use (CompleteProduct.state (CompleteProduct.config_device attrs)) before performed
  | create => exact use (CompleteProduct.rtnetlink _ (CompleteProduct.wg _ CompleteDeviceCreation.checked)) before performed
  | delete =>
    obtain ⟨_,_,_,post⟩ := RunnerSource.dispatch_checked .wgDelete w h before
    change runPrefix (Driver.dispatchObserved hooks .wgDelete) w h=(.ok (value,v),last) at performed
    rw [performed] at post
    exact post.1
  | «open» => exact use CompleteProduct.env_up before performed
  | down => exact use CompleteProduct.env_down before performed
  | transmit family addr payload opts => exact use (CompleteProduct.Traffic.syscallXmit family addr payload opts) before performed
  | receive family port message tos ll dest => exact use (CompleteProduct.Execution.inject family port message tos ll dest) before performed
  | flood count port family messages => exact use (CompleteProduct.Execution.flood count port family messages) before performed
  | batch items => exact use (CompleteProduct.Execution.batch items) before performed
  | dumpDevice ref => exact use (CompleteProduct.state (CompleteDump.device ref)) before performed
  | dumpStart fd ref => exact use (CompleteProduct.state (CompleteDump.start fd ref)) before performed
  | dumpReceive fd => exact use (CompleteProduct.state (CompleteDump.receive fd)) before performed
  | idle => exact use CompleteProduct.Execution.idle before performed
  | delivery => exact use CompleteProduct.delivery before performed

theorem Child.normal (child : Child action) (before : child.Entry h w)
    (performed : runPrefix action w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
  cases child with
  | family family => exact family.normal before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
