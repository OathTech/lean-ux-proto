import Leanux.Proofs.WG.Noise.DriverTagRetainedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Leanux.Proofs.WG.Configuration

def observe : ProductObs Int := do
  let (ret,observed) ← Traffic.observe
  liftPrefix (modifyAmbient fun w => {w with extraOut :=
    (["datagrams","replies","stats"].map (fun k => (k,observed.getObjValD k)))})
  socketCallOnWith (fun {_} a => liftPrefix a) LISTEN4_FD (pure ret)

def xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : ProductObs Int :=
  syscallXmitWith Traffic.multicast Traffic.transmit family addr payload opts

def dispatch (call : Syscall) : ProductObs Int :=
  dispatchWith retained
    (fun attrs => netlinkRequestWith (fun {_} a => liftPrefix a)
      (liftWGObserver (DriverTags.Configuration.observeDevice attrs)))
    (rtnetlinkRequestWith (fun {_} a => liftPrefix a) Environment.createObserved)
    (rtnetlinkRequestWith (fun {_} a => liftPrefix a) Environment.deleteObserved)
    xmit
    (fun family port message tos ll dest => socketCallOnWith (fun {_} a => liftPrefix a)
      SENDER_FD (Traffic.inject family port message tos ll dest))
    Traffic.flood Traffic.batch observe call

theorem observe_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory observe := by
  unfold observe
  apply (Traffic.observe_preserves entry).bind
  rintro ⟨ret,result⟩
  apply PrefixPreserves.bind
  · exact Outer.lift_ambient entry (modify fun w => {w with extraOut :=
      (["datagrams","replies","stats"].map (fun k => (k,result.getObjValD k)))})
  · intro _
    exact Outer.socketCallOn_tag_variant entry _ _ (PrefixPreserves.pure (safe entry) ret)

theorem observe_erases : ErasesPrefix observe (Leanux.dispatch .wgObserve) := by
  unfold observe Leanux.dispatch
  apply erasesPrefix_bind Traffic.observe_erases
  rintro ⟨ret,result⟩
  exact erasesPrefix_bind (erasesPrefix_lift _)
    (fun _ => Outer.socketCallOn_erases _ _ _ (erasesPrefix_pure ret))

theorem xmit_preserves (entry : TagMap) (family addr : Nat)
    (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (StateInv entry) ValidHistory (xmit family addr payload opts) :=
  syscallXmitWith_preserves (safe entry) (state_store entry) _ _
    (Traffic.multicast_preserves entry) (Traffic.transmit_preserves entry) family addr payload opts

theorem xmit_erases (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ErasesPrefix (xmit family addr payload opts)
      (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  unfold xmit syscallXmitWith Leanux.dispatch
  apply Outer.socketCallOn_erases
  repeat' first
    | (maintenance_head Traffic.multicast; exact Traffic.multicast_erases _ _)
    | (maintenance_head Traffic.transmit; exact Traffic.transmit_erases _ _ _ _)
    | control_audit_erases

theorem dispatch_preserves (entry : TagMap) (call : Syscall) :
    PrefixPreserves (StateInv entry) ValidHistory (dispatch call) := by
  apply dispatchWith_preserves
  · exact retained_preserves entry
  · intro attrs
    apply Outer.netlinkRequest_tag_variant entry
    exact Scheduler.native_observed entry _ (DriverTags.Configuration.observeDevice_preserves entry attrs)
  · exact Outer.rtnetlinkRequest_tag_variant entry _ (Environment.createObserved_preserves entry)
  · exact Outer.rtnetlinkRequest_tag_variant entry _ (Environment.deleteObserved_preserves entry)
  · exact xmit_preserves entry
  · intro family port message tos ll dest
    exact Outer.socketCallOn_tag_variant entry _ _
      (Traffic.inject_preserves entry family port message tos ll dest)
  · exact Traffic.flood_preserves entry
  · exact Traffic.batch_preserves entry
  · exact observe_preserves entry

theorem dispatch_erases (call : Syscall) : ErasesPrefix (dispatch call) (Leanux.dispatch call) := by
  cases call
  case wgSet attrs =>
    exact Outer.netlinkRequest_erases _ _
      (liftWGObserver_erases (DriverTags.Configuration.observeDevice_erases attrs))
  case wgCreate =>
    exact Outer.rtnetlinkRequest_erases _ _ Environment.createObserved_erases
  case wgDelete =>
    exact Outer.rtnetlinkRequest_erases _ _ Environment.deleteObserved_erases
  case wgXmit family addr payload opts => exact xmit_erases family addr payload opts
  case wgInject family port message tos ll dest =>
    exact Outer.socketCallOn_erases _ _ _ (Traffic.inject_erases family port message tos ll dest)
  case wgFlood count port family messages => exact Traffic.flood_erases count port family messages
  case wgBatch items waitMs => exact Traffic.batch_erases items
  case wgObserve => exact observe_erases
  all_goals simp only [dispatch,dispatchWith]
  all_goals exact retained_erases _

def syscall (call : Syscall) : ProductObs Int :=
  syscallWith (fun {_} a => liftPrefix a) (dispatch call)
    (Scheduled.deferred .sendAll) (Scheduled.deferred .idle)
    (liftPrefix Env.routeIntoWg0) (Scheduled.deferred .afterXmit)
    (Scheduled.deferred .afterAdvance) Environment.cleanupObserved call

theorem syscall_preserves (entry : TagMap) (call : Syscall) :
    PrefixPreserves (StateInv entry) ValidHistory (syscall call) :=
  SyscallSource.preserves (safe entry) (state_store entry) call _ _ _ _ _ _ _
    (dispatch_preserves entry call)
    (Scheduled.deferred_preserves entry .sendAll)
    (Scheduled.deferred_preserves entry .idle)
    (lift_product_store entry _ routeIntoWg0_sameKernel)
    (Scheduled.deferred_preserves entry .afterXmit)
    (Scheduled.deferred_preserves entry .afterAdvance)
    (Environment.cleanupObserved_preserves entry)

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  unfold syscall syscallWith Leanux.syscall
  repeat' first
    | (maintenance_head dispatch; exact dispatch_erases _)
    | (maintenance_head Scheduled.deferred; exact Scheduled.deferred_erases _)
    | (maintenance_head Environment.cleanupObserved; exact Environment.cleanupObserved_erases)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
    | control_audit_erases

end Leanux.Proofs.WG.Noise.DriverTags.Syscalls
