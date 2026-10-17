import Leanux.Proofs.WG.Lifetimes.TxCallSource
import Leanux.Proofs.WG.Queues.JointSyscalls

/-! An explicit selector for the original dispatch arms. Every source
constructor is listed; traffic and routing configuration have separate slots.
The retained slots delegate their complete original action, without a copied
interpreter or a default execution arm. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues

/-- These and only these constructors delegate to the retained-arm callback. -/
def DispatchRetained : Syscall → Prop
  | .wgSet .. | .wgCreate | .wgDelete | .wgXmit .. | .wgInject ..
  | .wgFlood .. | .wgBatch .. | .wgObserve => False
  | _ => True

def dispatchWith {E : Type}
    (retained : Syscall → PrefixM E Int)
    (set : DeviceAttrs → PrefixM E Int) (create delete : PrefixM E Int)
    (xmit : Nat → Nat → List UInt8 → Env.XmitOpts → PrefixM E Int)
    (inject : Nat → Nat → List UInt8 → Nat → Bool → Nat → PrefixM E Int)
    (flood : Nat → Nat → Nat → List (List UInt8) → PrefixM E Int)
    (batch : List Env.BatchItem → PrefixM E Int) (observe : PrefixM E Int) : Syscall → PrefixM E Int
  | call@(.eventfd2 ..) => retained call
  | call@(.dup ..) => retained call
  | call@(.dup3 ..) => retained call
  | call@(.close ..) => retained call
  | call@(.read ..) => retained call
  | call@(.write ..) => retained call
  | call@(.pipe2 ..) => retained call
  | call@(.fcntl ..) => retained call
  | call@(.epollCreate1 ..) => retained call
  | call@(.epollCtl ..) => retained call
  | call@(.epollWait ..) => retained call
  | call@(.wgGet ..) => retained call
  | call@(.wgGetStart ..) => retained call
  | call@(.wgGetRecv) => retained call
  | call@(.wgUp) => retained call
  | call@(.wgSetMtu ..) => retained call
  | call@(.wgDeladdr ..) => retained call
  | call@(.wgDelroute ..) => retained call
  | call@(.wgAddroute ..) => retained call
  | call@(.wgAddaddr ..) => retained call
  | call@(.wgAdvance ..) => retained call
  | call@(.wgDown) => retained call
  | call@(.wgNetnsClose) => retained call
  | call@(.seccompInstall ..) => retained call
  | call@(.seccompProbe ..) => retained call
  | call@(.seccompPrctl ..) => retained call
  | call@(.seccompCapdrop) => retained call
  | call@(.seccompQuery ..) => retained call
  | .wgSet attrs => set attrs
  | .wgCreate => create
  | .wgDelete => delete
  | .wgXmit family addr payload opts => xmit family addr payload opts
  | .wgInject family port message tos ll dest => inject family port message tos ll dest
  | .wgFlood count port family messages => flood count port family messages
  | .wgBatch items _ => batch items
  | .wgObserve => observe

/-- The original RX observer is an exact specialization, including socket
wrappers, every returned errno, and the original observe postprocessing. -/
theorem rxDispatch_source (call : Syscall) :
    RxHistory.syscallDispatch call = dispatchWith RxHistory.syscallDispatch
      (fun attrs => RxHistory.audit (dispatchAudit (.wgSet attrs)))
      (RxHistory.audit (dispatchAudit .wgCreate)) (RxHistory.audit (dispatchAudit .wgDelete))
      (fun family addr payload opts => RxHistory.audit
        (syscallXmitWith xmitMulticastLoopAudit
          (fun family addr packets mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
          family addr payload opts))
      (fun family port message tos ll dest => RxHistory.socketCallOn SENDER_FD
        (RxHistory.inject family port message tos ll dest))
      RxHistory.flood RxHistory.batch (RxHistory.syscallDispatch .wgObserve) call := by
  cases call <;> rfl

/-- Routing set/create/delete keep their original completion observers. The
other selected arms retain the actual RX journal through its canonical focus. -/
theorem jointDispatch_source (call : Syscall) :
    RoutingJoint.dispatch call = dispatchWith RoutingJoint.dispatch
      RoutingJoint.dispatchSet RoutingJoint.dispatchCreate RoutingJoint.dispatchDelete
      (fun family addr payload opts => RoutingJoint.rxAction (RxHistory.audit
        (syscallXmitWith xmitMulticastLoopAudit
          (fun family addr packets mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
          family addr payload opts)))
      (fun family port message tos ll dest => RoutingJoint.rxAction
        (RxHistory.socketCallOn SENDER_FD (RxHistory.inject family port message tos ll dest)))
      (fun count port family messages => RoutingJoint.rxAction (RxHistory.flood count port family messages))
      (fun items => RoutingJoint.rxAction (RxHistory.batch items))
      (RoutingJoint.rxAction (RxHistory.syscallDispatch .wgObserve)) call := by
  cases call <;> rfl

section
variable {E F : Type}
    (retained : Syscall → PrefixM E Int)
    (set : DeviceAttrs → PrefixM E Int) (create delete : PrefixM E Int)
    (xmit : Nat → Nat → List UInt8 → Env.XmitOpts → PrefixM E Int)
    (inject : Nat → Nat → List UInt8 → Nat → Bool → Nat → PrefixM E Int)
    (flood : Nat → Nat → Nat → List (List UInt8) → PrefixM E Int)
    (batch : List Env.BatchItem → PrefixM E Int) (observe : PrefixM E Int)

/-- Preservation is required only at the selected source arm. In particular,
the retained callback is never assumed to handle a hidden poll-bearing arm. -/
theorem dispatchWith_preserves {I : List E → World → Prop} {S : List E → Prop}
    (ho : ∀ call, DispatchRetained call → PrefixPreserves I S (retained call))
    (hs : ∀ attrs, PrefixPreserves I S (set attrs))
    (hc : PrefixPreserves I S create) (hd : PrefixPreserves I S delete)
    (hx : ∀ family addr payload opts, PrefixPreserves I S (xmit family addr payload opts))
    (hi : ∀ family port message tos ll dest, PrefixPreserves I S (inject family port message tos ll dest))
    (hf : ∀ count port family messages, PrefixPreserves I S (flood count port family messages))
    (hb : ∀ items, PrefixPreserves I S (batch items)) (hv : PrefixPreserves I S observe)
    (call : Syscall) :
    PrefixPreserves I S (dispatchWith retained set create delete xmit inject flood batch observe call) := by
  cases call
  case wgSet attrs => exact hs attrs
  case wgCreate => exact hc
  case wgDelete => exact hd
  case wgXmit family addr payload opts => exact hx family addr payload opts
  case wgInject family port message tos ll dest => exact hi family port message tos ll dest
  case wgFlood count port family messages => exact hf count port family messages
  case wgBatch items _ => exact hb items
  case wgObserve => exact hv
  all_goals exact ho _ True.intro

/-- Exact callback projections give the same full dispatch result, state,
projected journal and Stop for arbitrary incoming histories. -/
theorem dispatchWith_projects (ρ : E → Option F)
    (retained' : Syscall → PrefixM F Int)
    (set' : DeviceAttrs → PrefixM F Int) (create' delete' : PrefixM F Int)
    (xmit' : Nat → Nat → List UInt8 → Env.XmitOpts → PrefixM F Int)
    (inject' : Nat → Nat → List UInt8 → Nat → Bool → Nat → PrefixM F Int)
    (flood' : Nat → Nat → Nat → List (List UInt8) → PrefixM F Int)
    (batch' : List Env.BatchItem → PrefixM F Int) (observe' : PrefixM F Int)
    (ho : ∀ call, DispatchRetained call → ProjectsPrefix ρ id (retained call) (retained' call))
    (hs : ∀ attrs, ProjectsPrefix ρ id (set attrs) (set' attrs))
    (hc : ProjectsPrefix ρ id create create') (hd : ProjectsPrefix ρ id delete delete')
    (hx : ∀ family addr payload opts, ProjectsPrefix ρ id (xmit family addr payload opts) (xmit' family addr payload opts))
    (hi : ∀ family port message tos ll dest, ProjectsPrefix ρ id
      (inject family port message tos ll dest) (inject' family port message tos ll dest))
    (hf : ∀ count port family messages, ProjectsPrefix ρ id
      (flood count port family messages) (flood' count port family messages))
    (hb : ∀ items, ProjectsPrefix ρ id (batch items) (batch' items))
    (hv : ProjectsPrefix ρ id observe observe') (call : Syscall) :
    ProjectsPrefix ρ id (dispatchWith retained set create delete xmit inject flood batch observe call)
      (dispatchWith retained' set' create' delete' xmit' inject' flood' batch' observe' call) := by
  cases call
  case wgSet attrs => exact hs attrs
  case wgCreate => exact hc
  case wgDelete => exact hd
  case wgXmit family addr payload opts => exact hx family addr payload opts
  case wgInject family port message tos ll dest => exact hi family port message tos ll dest
  case wgFlood count port family messages => exact hf count port family messages
  case wgBatch items _ => exact hb items
  case wgObserve => exact hv
  all_goals exact ho _ True.intro
end

end Leanux.Proofs.WG.Lifetimes
