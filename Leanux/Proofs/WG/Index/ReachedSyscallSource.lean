import Leanux.Proofs.WG.Index.ReachedTrafficSource
import Leanux.Proofs.WG.Index.ReachedDeferredEntrySource
import Leanux.Proofs.WG.Index.ReachedOrdinaryControlSource
import Leanux.Proofs.WG.Noise.DriverTagSyscallSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedTraffic
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem xmit_ready (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World=>TimerCore.Ready w.wg) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  apply PollCore.original _ (DriverTags.Syscalls.xmit family addr payload opts) _
    (DriverTags.Syscalls.xmit_erases family addr payload opts)
  apply syscallXmitWith_preserves (fun _ _ _=>True.intro)
    (fun _ w v same pre=>TransmitCore.ready_product_store
      (w:={w with wg:=w.wg}) (v:={w with wg:=v.wg})
      (by simp only [productStoreView,same]) pre)
  · intro f a
    exact PollCore.lifted _ _
      (((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) f a).wp
        (fun s : ProductStore43=>TimerCore.Ready {dev:=s.2.2.2.dev}))
  · intro f a packets mtu
    exact PollCore.lifted _ _ (PublicationPoll.native_product _ _ (TransmitCore.wgXmit_ready f a packets mtu))

theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) := by
  apply ReachedControls.original_pair _ _ (RxHistory.syscallDispatch_erases (.wgXmit family addr payload opts))
    (fun _=>HolderEntryDispatch.xmit family addr payload opts)
  intro cs w h pre result v run
  exact ((hoare_iff_run _ _ _).mp (xmit_ready family addr payload opts) w result v
    ⟨pre.1.1.2.2,pre.2⟩ run).2

theorem entry_wait {α : Type} (action : RxHistory.Obs α)
    (checked : ∀ cs before,
      PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs [] h w) OwnerChecks.Safe action
        (fun _ k v=>∃suffix,k=before++suffix ∧
          Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) [] k v)) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe action := by
  intro w h pre
  obtain ⟨cs,pre⟩ := pre
  obtain ⟨suffix,history,safe,post⟩ := checked cs h w h ⟨rfl,pre⟩
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error stop=>trivial
  | ok out=>
    rw [run] at post
    obtain ⟨fresh,_,post⟩ := post
    exact ⟨remaining cs (NapiCarrier.removedPackets fresh),post⟩

theorem socketCallOn_preserves_entry_variant (fd : Nat) (body : RxHistory.Obs Int)
    (keep : PrefixPreserves Reached.AnyEntry OwnerChecks.Safe body) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  apply PrefixPreserves.bind
    (entry_lift _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ pre=>pre)))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure Reached.anyEntry_safe _
  · intro _
    exact keep.bind (fun ret=>(entry_lift _
      (fun initial=>productFS_spec _ _ (fun _ _ _ _ pre=>pre))).bind
        (fun _=>PrefixPreserves.pure Reached.anyEntry_safe ret))

theorem observe :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe RxHistory.observe := by
  unfold RxHistory.observe
  exact (entry_wait _ (fun cs before=>ReachedDeferred.entry_idle cs [] before)).bind
    (fun _=>entry_lift _ (observeTail_sameKernel.of_factor
      (fun s : ProductStore43=>s.2.2.2) _ (fun _=>rfl)))

theorem observe_dispatch :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgObserve) := by
  change PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (do
    let (ret,out) ← RxHistory.observe
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=
      (["datagrams","replies","stats"].map (fun key=>(key,out.getObjValD key)))})
    RxHistory.socketCallOn LISTEN4_FD (pure ret))
  apply observe.bind
  rintro ⟨ret,out⟩
  exact (entry_lift _ (fun initial=>productAmbient_spec _ _ (fun _ _ pre=>pre))).bind
    (fun _=>socketCallOn_preserves_entry_variant _ _ (PrefixPreserves.pure Reached.anyEntry_safe ret))

theorem route :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.audit routeIntoWg0Audit) :=
  ReachedControls.configuration_pair _ _ (RxHistory.audit_erases routeIntoWg0Audit_erases)
    (fun _=>HolderEntryControls.route)
    (fun cs=>LifecycleEnvironment.product_entry cs [] _ routeIntoWg0_sameKernel)

theorem dispatch (call : Syscall) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  rw [rxDispatch_source]
  apply dispatchWith_preserves
  · exact ReachedControls.retained
  · exact ReachedControls.configuration
  · exact ReachedControls.create
  · exact ReachedControls.delete
  · exact xmit
  · intro family port msg tos ll dest
    exact socketCallOn_preserves_entry_variant _ _ (inject family port msg tos ll dest)
  · exact flood
  · exact batch
  · exact observe_dispatch

theorem syscall (call : Syscall) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscall call) := by
  rw [Leanux.Proofs.WG.Configuration.syscallRx_factor]
  exact SyscallSource.preserves Reached.anyEntry_safe Reached.anyEntry_store call _ _ _ _ _ _ _
    (dispatch call)
    (entry_wait _ (fun cs before=>ReachedDeferred.entry_sendAll cs [] before))
    (entry_wait _ (fun cs before=>ReachedDeferred.entry_idle cs [] before))
    route (entry_wait _ (fun cs before=>ReachedDeferred.entry_afterXmit cs [] before))
    (entry_wait _ (fun cs before=>ReachedDeferred.entry_afterAdvance cs [] before))
    ReachedControls.cleanup

end Leanux.Proofs.WG.Index.ReachedTraffic
