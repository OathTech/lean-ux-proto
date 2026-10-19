import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryTraffic
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Exact initialized runner transport for native replay-entry coherence.
The nonreceive dispatch frame is reused only at source arms without polling;
receive-capable arms compose the actual observed callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs TransmitSecurity.Driver
open Configuration (socketCallOnWith netlinkRequestWith rtnetlinkRequestWith)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem dispatch_erases (call : Syscall) :
    ErasesPrefix (dispatchObserved hooks call) (Leanux.dispatch call) := by
  apply product_native_result (dispatch_projects native_projects call)
    (dispatch_projects HandshakeSecurity.NativeDriver.nonce_projection call)
  rw [nonce_dispatchObserved_eq]
  exact TransmitSecurity.Nonce.dispatchObserved_erases call

theorem quiet_dispatch (call : Syscall)
    (quiet : dispatchObserved hooks call = dispatchObserved quietHooks call)
    (noReceive : SyscallObservers.NoReceiveDispatch call) : ProductSafe (dispatchObserved hooks call) := by
  apply product_observed _ _ (dispatch_erases call) _ (SyscallObservers.dispatch_noReceive_ordinary call noReceive)
  rw [quiet]
  exact dispatch_history (quiet_history Safe).actors call

private theorem quiet_up : envUpObserved hooks = envUpObserved quietHooks := rfl
private theorem quiet_down : envDownObserved hooks = envDownObserved quietHooks := by
  rw [envDown_lift hooks rfl rfl,envDown_lift quietHooks rfl rfl]
private theorem quiet_delete : envDeleteObserved hooks = envDeleteObserved quietHooks := by
  rw [envDelete_lift hooks rfl rfl rfl,envDelete_lift quietHooks rfl rfl rfl]
private theorem quiet_config (attrs : DeviceAttrs) : configDevice hooks attrs = configDevice quietHooks attrs := rfl

theorem retained (call : Syscall) (kept : DispatchRetained call) :
    ProductSafe (retainedObserved hooks call) := by
  have source : retainedObserved hooks call = dispatchObserved hooks call := by
    cases call <;> simp_all only [DispatchRetained,dispatchObserved,dispatchWith] <;> contradiction
  rw [source]
  apply quiet_dispatch
  · cases call <;> simp_all only [DispatchRetained,dispatchObserved,dispatchWith,retainedObserved,quiet_up,quiet_down] <;> contradiction
  · cases call <;> simp_all only [DispatchRetained,SyscallObservers.NoReceiveDispatch] <;> contradiction

theorem product_fs (action : FS.M α) : ProductSafe (liftPrefix (liftFS action)) :=
  product_same _ (fun initial => productFS_spec action (fun w => snapshot w.wg = initial)
    (fun _ _ _ _ hi => hi))

theorem socket_call (fd : Nat) (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply product_bind (product_fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (product_fs (fdput f)) (fun _ => product_pure ret))

theorem observe : ProductSafe (observeObserved hooks) :=
  product_bind idle_timers (fun _ =>
    DeliverySource.observe_preserves (fun _ _ hi => hi.2) product_store _ deliver)

theorem dispatch_observe : ProductSafe (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply product_bind observe
  rintro ⟨ret,json⟩
  exact product_bind (product_ambient _) (fun _ => socket_call _ _ (product_pure ret))

theorem dispatch (call : Syscall) : ProductSafe (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained
  · intro attrs
    change ProductSafe (dispatchObserved hooks (.wgSet attrs))
    apply quiet_dispatch (.wgSet attrs) _ trivial
    exact congrArg (fun body : WGPrefix Event Int => netlinkRequestWith
      (fun {α} (action : Leanux.M α) => (liftPrefix action : PrefixM Event α))
      (liftWGObserver body)) (quiet_config attrs)
  · change ProductSafe (dispatchObserved hooks .wgCreate)
    exact quiet_dispatch .wgCreate (by simp only [dispatchObserved,dispatchWith]) trivial
  · change ProductSafe (dispatchObserved hooks .wgDelete)
    apply quiet_dispatch .wgDelete _ trivial
    exact congrArg (fun body : PrefixM Event Int => rtnetlinkRequestWith
      (fun {α} (action : Leanux.M α) => (liftPrefix action : PrefixM Event α)) body) quiet_delete
  · exact syscall_xmit
  · intro family port message tos ll dest
    exact socket_call _ _ (inject family port message tos ll dest)
  · exact flood
  · exact batch
  · exact dispatch_observe

theorem syscall (call : Syscall) : ProductSafe (syscallObserved hooks call) :=
  SyscallSource.preserves (I := ProductInv) (S := Safe)
    (fun _ _ hi => hi.2) product_wg_store call _ _ _ _ _ _ _
    (dispatch call) send_workers idle_timers
    (product_same _ EnvFrames.routeIntoWg0_sameSnapshot) after_xmit after_advance
    (product_same _ EnvFrames.netnsCleanup_sameSnapshot)

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (executeObserved hooks trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv Safe
    (fun _ _ hi => hi.2) product_wg_store (syscallObserved hooks) syscall trace placeholders
  intro w same
  refine ⟨?_,safe_empty⟩
  have snap := congrArg Keypairs.snapshotOfWGStoreView same
  change snapshot w.wg = snapshot (Runner.initialWG trace.net trace.bare) at snap
  change ReplayRefusal.SnapshotCoherent (snapshot w.wg)
  rw [snap,Keypairs.initial_snapshot]
  exact ReplayRefusal.snapshot_empty _

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
