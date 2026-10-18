import Leanux.Proofs.WG.TransmitSecurity.NonceOuter

/-! The complete native dispatcher, with nonce allocations observed at each
actual sending-counter reservation. No original guard or failure is removed. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

def retainedObserved (call : Syscall) : PrefixM Allocation Int :=
  match call with
  | .wgUp => socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD envUpObserved
  | _ => liftPrefix (Leanux.dispatch call)

def observeObserved : PrefixM Allocation (Int × Lean.Json) := do
  idleTimersObserved
  liftPrefix Environment.observeTail

def dispatchObserveObserved : PrefixM Allocation Int := do
  let (ret, observed) ← observeObserved
  liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
  socketCallOnWith (fun {_} a => liftPrefix a) LISTEN4_FD (pure ret)

def dispatchSetObserved (attrs : DeviceAttrs) : PrefixM Allocation Int :=
  netlinkRequestWith (fun {_} a => liftPrefix a) (liftWGObserver (configDevice attrs))

def dispatchCreateObserved : PrefixM Allocation Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a) (liftPrefix (liftWG wgCreate))

def dispatchDeleteObserved : PrefixM Allocation Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a) (liftPrefix Env.wgDelete)

def dispatchObserved (call : Syscall) : PrefixM Allocation Int :=
  dispatchWith retainedObserved dispatchSetObserved dispatchCreateObserved dispatchDeleteObserved
    syscallXmitObserved (fun family port message tos ll dest =>
      socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD (injectObserved family port message tos ll dest))
    floodObserved batchObserved dispatchObserveObserved call

theorem retainedObserved_safe (call : Syscall) (retained : DispatchRetained call) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (retainedObserved call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ envUpObserved_safe
  · simp only [retainedObserved]
    exact Outer.lift_spec _ (fun h => Frames.quiet_dispatch call h retained up)

theorem retainedObserved_erases (call : Syscall) :
    ErasesPrefix (retainedObserved call) (Leanux.dispatch call) := by
  cases call
  case wgUp => exact socketCallOnWith_erases _ envUpObserved_erases
  all_goals exact erasesPrefix_lift _

theorem observeObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup observeObserved :=
  idleTimersObserved_safe.bind (fun _ => Frames.stored observeTail_sameKernel)

theorem observeObserved_erases : ErasesPrefix observeObserved Env.observe := by
  rw [Environment.observe_eq]
  unfold observeObserved
  apply erasesPrefix_bind idleTimersObserved_erases
  intro _
  exact erasesPrefix_lift _

theorem dispatchObserveObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup dispatchObserveObserved := by
  apply observeObserved_safe.bind
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (PrefixPreserves.pure (fun _ _ hi => hi.nodup) ret)

theorem dispatchObserved_safe (call : Syscall) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (dispatchObserved call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ retainedObserved_safe
    (fun attrs => Outer.netlinkRequest _ (configDevice_safe attrs).liftWGObserver)
    (Outer.rtnetlinkRequest _ (Frames.product_native Frames.create_device))
    (Outer.rtnetlinkRequest _ (Frames.product_lift Frames.env_delete))
    syscallXmitObserved_safe
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (injectObserved_safe family port message tos ll dest))
    floodObserved_safe batchObserved_safe dispatchObserveObserved_safe call


theorem dispatchObserveObserved_erases :
    ErasesPrefix dispatchObserveObserved (Leanux.dispatch .wgObserve) := by
  change ErasesPrefix _ (do
    let (ret, observed) ← Env.observe
    modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)}
    Leanux.socketCallOn LISTEN4_FD (pure ret))
  unfold dispatchObserveObserved
  apply erasesPrefix_bind observeObserved_erases
  rintro ⟨ret,observed⟩
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro _
  exact socketCallOnWith_erases _ (erasesPrefix_pure _)

theorem dispatchObserved_erases (call : Syscall) :
    ErasesPrefix (dispatchObserved call) (Leanux.dispatch call) := by
  cases call
  case wgSet attrs => exact netlinkRequestWith_erases (liftWGObserver_erases (configDevice_erases attrs))
  case wgCreate => exact Outer.rtnetlinkRequest_erases (erasesPrefix_lift _)
  case wgDelete => exact Outer.rtnetlinkRequest_erases (erasesPrefix_lift _)
  case wgXmit family addr payload opts => exact syscallXmitObserved_erases family addr payload opts
  case wgInject family port message tos ll dest =>
    exact socketCallOnWith_erases _ (injectObserved_erases family port message tos ll dest)
  case wgFlood count port family messages => exact floodObserved_erases count port family messages
  case wgBatch items _ => exact batchObserved_erases items
  case wgObserve => exact dispatchObserveObserved_erases
  all_goals dsimp only [dispatchObserved,dispatchWith]
  all_goals exact retainedObserved_erases _

end Leanux.Proofs.WG.TransmitSecurity.Nonce
