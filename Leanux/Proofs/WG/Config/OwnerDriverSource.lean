import Leanux.Proofs.WG.Config.OwnerDriverFrames
import Leanux.Proofs.WG.Config.DispatchRulesSource
import Leanux.Proofs.WG.Config.ConfiguredLifecycleSource
import Leanux.Proofs.WG.Config.ConfiguredDeviceSource
import Leanux.Proofs.WG.Index.ReachedSyscallSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerDriver
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem pair_normal {α : Type} (observed : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix observed original)
    (account : PrefixPreserves Index.Reached.AnyEntry OwnerChecks.Safe observed)
    (normal : ∀ w h, Inv h w → ∀ result v, original.run w=.ok (result,v) → OptionalReady v.wg) :
    PrefixPreserves Inv OwnerChecks.Safe observed := by
  intro w h pre
  obtain ⟨suffix,append,valid,post⟩ := account w h pre.1
  refine ⟨suffix,append,valid,?_⟩
  cases run : (runPrefix observed w h).1 with
  | error stop => trivial
  | ok out =>
    rw [run] at post
    exact ⟨post,normal w h pre out.1 out.2 ((erase w h).symm.trans run)⟩

theorem pair {α : Type} (observed : RxHistory.Obs α) (original : Leanux.M α)
    (erase : ErasesPrefix observed original)
    (account : PrefixPreserves Index.Reached.AnyEntry OwnerChecks.Safe observed)
    (normal : Preserves (fun w : World=>OptionalReady w.wg) original) :
    PrefixPreserves Inv OwnerChecks.Safe observed :=
  pair_normal observed original erase account
    (fun w _ pre result v run=>(hoare_iff_run _ _ _).mp normal w result v pre.2 run)

theorem absent_device (attrs : DeviceAttrs) (g v : WGWorld) (a b : Ambient) (result : Int)
    (absent : g.dev=none)
    (run : ((wgSetDevice attrs).run g).run a=.ok ((result,v),b)) : v.dev=none := by
  obtain ⟨_,_,_,post⟩ := Configuration.wgSetDeviceObserved_absent [] attrs g a []
    ⟨rfl,by simp only [routingView,absent,Option.map_none]⟩
  have observed := (Configuration.wgSetDeviceObserved_erases attrs g a []).trans run
  rw [observed] at post
  have absentView : routingView v=none := post.2
  cases present : v.dev with
  | none => rfl
  | some d => simp only [routingView,present,Option.map_some] at absentView; cases absentView

theorem device_optional (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : Configuration.DeviceAddressShape attrs) :
    Preserves (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ OptionalReady g) (wgSetDevice attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (Index.ConfigurationIndex.device_entry cs loans attrs)
    g a result v b pre.1 run,?_⟩
  cases present : g.dev with
  | none =>
    intro d final
    rw [absent_device attrs g v a b result present run] at final
    cases final
  | some d =>
    have ending := (hoare_iff_run_ambient _ _ _).mp (OwnerConfiguration.device_entry cs loans attrs shape)
      g a result v b ⟨pre.1,d,present,pre.2 d present⟩ run
    obtain ⟨out,device,ready⟩ := ending.2
    intro d final
    rw [device] at final
    cases final
    exact ready

theorem dump_contracts : DumpInvariant.Contracts OptionalReady where
  stable w v same pre := by
    have device : v.dev=w.dev := congrArg WGStoreView.dev same
    intro d present
    exact pre d (device.symm.trans present)
  acquire pid := optionalReady_native _ (ProjectedRetainsRoutingCall.of_same (peerGet_routing pid))
    (BaseCoherence.peerGet_view pid)
  release pid := optionalReady_native _ (peerPut_retainsRouting pid) (BaseCoherence.peerPut_view pid)

theorem dispatch_contracts : DispatchRules.Contracts OptionalReady where
  stable := optional_store
  dump call := DumpInvariant.call dump_contracts call
  dumpFrame action same := DumpInvariant.frame dump_contracts action same
  up := optionalReady_envUp
  down := optionalReady_envDown
  mtu n := optionalReady_product _ (ProjectedRetainsRoutingCall.of_same (envSetMtu_routing n)) (mtu_base n)

theorem configuration (attrs : DeviceAttrs) (shape : Configuration.DeviceAddressShape attrs) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) := by
  apply pair_normal _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedControls.configuration attrs)
  intro w h pre result v run
  obtain ⟨cs,account⟩ := pre.1
  have native := Index.DumpCore.netlinkRequest_preserves
    (fun g=>Index.ConfigurationIndex.Entry cs [] g ∧ OptionalReady g) _
      (PublicationPoll.native_product _ _ (device_optional cs [] attrs shape))
  exact ((hoare_iff_run _ _ _).mp native w result v
    ⟨Index.ReachedControls.entry_configuration account,pre.2⟩ run).2

theorem xmit_optional (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World=>OptionalReady w.wg) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  apply Index.PollCore.original _ (DriverTags.Syscalls.xmit family addr payload opts) _
    (DriverTags.Syscalls.xmit_erases family addr payload opts)
  apply syscallXmitWith_preserves (fun _ _ _=>True.intro)
    (fun _ w v same pre=>optional_store w.wg v.wg same pre)
  · intro f a
    exact Index.PollCore.lifted _ _
      (optionalReady_productStore _ ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) f a))
  · intro f a packets mtu
    exact Index.PollCore.lifted _ _ (optionalReady_lift _
      (optionalReady_native _ (wgXmit_routing f a packets mtu) (BaseCoherence.wgXmit_view f a packets mtu)))

theorem observe_optional :
    Preserves (fun w : World=>OptionalReady w.wg) Env.observe := by
  rw [Environment.observe_eq]
  exact preserves_bind (optionalReady_deferred .idle)
    (fun _=>optionalReady_productStore _ observeTail_sameKernel)

theorem observe_dispatch_optional :
    Preserves (fun w : World=>OptionalReady w.wg) (Leanux.dispatch .wgObserve) := by
  change Preserves _ (do
    let (ret,out) ← Env.observe
    modifyAmbient fun w=>{w with extraOut:=
      (["datagrams","replies","stats"].map fun key=>(key,out.getObjValD key))}
    socketCallOn LISTEN4_FD (pure ret))
  apply preserves_bind observe_optional
  rintro ⟨ret,out⟩
  exact preserves_bind (productAmbient_spec _ _ (fun _ _ pre=>pre))
    (fun _=>Index.DumpCore.socketCallOn_preserves _ _ _ (preserves_pure ret))

theorem dispatch (call : Syscall) (shape : Configuration.SyscallAddressShape call) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  cases call
  case wgSet attrs => exact configuration attrs shape
  case wgCreate =>
    apply pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedControls.create)
    exact DispatchRules.rtnetlink_retained _ dispatch_contracts _ (optionalReady_lift _ optionalReady_create)
  case wgDelete =>
    apply pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedControls.delete)
    exact DispatchRules.rtnetlink_retained _ dispatch_contracts _ optionalReady_delete
  case wgXmit family addr payload opts =>
    exact pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedTraffic.xmit family addr payload opts)
      (xmit_optional family addr payload opts)
  case wgInject family port msg tos ll dest =>
    apply pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedTraffic.dispatch _)
    exact Index.DumpCore.socketCallOn_preserves _ _ _ (optionalReady_inject family port msg tos ll dest)
  case wgFlood count port family messages =>
    exact pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedTraffic.flood count port family messages)
      (optionalReady_flood count port family messages)
  case wgBatch items poll =>
    exact pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedTraffic.batch items)
      (optionalReady_batch items)
  case wgObserve =>
    exact pair _ _ (RxHistory.syscallDispatch_erases _) Index.ReachedTraffic.observe_dispatch observe_dispatch_optional
  all_goals
    exact pair _ _ (RxHistory.syscallDispatch_erases _) (Index.ReachedTraffic.dispatch _)
      (DispatchRules.retained _ dispatch_contracts _ True.intro)

theorem syscall (call : Syscall) (shape : Configuration.SyscallAddressShape call) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscall call) := by
  rw [Configuration.syscallRx_factor]
  apply SyscallSource.preserves safe store call
  · exact dispatch call shape
  · exact pair _ _ RxHistory.runSendWorkers_erases
      (Index.ReachedTraffic.entry_wait _ (fun cs before=>Index.ReachedDeferred.entry_sendAll cs [] before))
      (optionalReady_deferred .sendAll)
  · exact pair _ _ RxHistory.idleTimers_erases
      (Index.ReachedTraffic.entry_wait _ (fun cs before=>Index.ReachedDeferred.entry_idle cs [] before))
      (optionalReady_deferred .idle)
  · exact pair _ _ (RxHistory.audit_erases routeIntoWg0Audit_erases) Index.ReachedTraffic.route
      (optionalReady_productStore _ routeIntoWg0_sameKernel)
  · exact pair _ _ RxHistory.afterXmit_erases
      (Index.ReachedTraffic.entry_wait _ (fun cs before=>Index.ReachedDeferred.entry_afterXmit cs [] before))
      (optionalReady_deferred .afterXmit)
  · exact pair _ _ RxHistory.afterAdvance_erases
      (Index.ReachedTraffic.entry_wait _ (fun cs before=>Index.ReachedDeferred.entry_afterAdvance cs [] before))
      (optionalReady_deferred .afterAdvance)
  · exact pair _ _ (RxHistory.audit_erases envNetnsCleanupAudit_erases) Index.ReachedControls.cleanup
      optionalReady_cleanup

end Leanux.Proofs.WG.Config.OwnerDriver
