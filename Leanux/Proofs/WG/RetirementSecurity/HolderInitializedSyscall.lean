import Leanux.Proofs.WG.RetirementSecurity.HolderInitializedSource

/-! The complete native syscall family, including return-to-user work, keeps
exact allocation credit. Every case uses its own actual source contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem dispatch (call : Syscall) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  cases call with
  | wgSet attrs=>exact fixed (fun _=>HolderOuter.dispatch_configure attrs)
  | wgUp=>exact fixed (fun _=>HolderOuter.dispatch_up)
  | wgDown=>exact fixed (fun _=>HolderOuter.dispatch_down)
  | wgCreate=>exact fixed (fun _=>HolderOuter.dispatch_create)
  | wgDelete=>exact fixed (fun _=>HolderOuter.dispatch_delete)
  | wgGet ref=>exact fixed (fun _=>HolderOuter.dump_get ref)
  | wgGetStart ref=>exact fixed (fun _=>HolderOuter.dump_start ref)
  | wgGetRecv=>exact fixed (fun _=>HolderOuter.dump_receive)
  | wgSetMtu n=>exact fixed (fun _=>HolderOuter.dispatch_mtu n)
  | wgXmit family addr payload opts=>exact fixed (fun _=>HolderOuter.dispatch_xmit family addr payload opts)
  | wgDeladdr family=>exact fixed (fun _=>HolderOuter.dispatch_deladdr family)
  | wgDelroute family named dst plen oif kind metric=>
    exact fixed (fun _=>HolderOuter.dispatch_delroute family named dst plen oif kind metric)
  | wgAddroute dst plen oif kind metric mtu flags=>
    exact fixed (fun _=>HolderOuter.dispatch_addroute dst plen oif kind metric mtu flags)
  | wgAddaddr addr plen=>exact fixed (fun _=>HolderOuter.dispatch_addaddr addr plen)
  | wgAdvance ticks=>exact fixed (fun _=>HolderOuter.dispatch_advance ticks)
  | wgNetnsClose=>exact fixed (fun _=>HolderOuter.dispatch_namespace)
  | wgInject family port msg tos ll dest=>exact socket _ _ (inject family port msg tos ll dest)
  | wgFlood count port family messages=>exact flood count port family messages
  | wgBatch items _=>exact batch items
  | wgObserve=>exact observe_dispatch
  | eventfd2 _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | dup _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | dup3 _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | close _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | read _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | write _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | pipe2 _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | fcntl _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | epollCreate1 _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | epollCtl _ _ _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | epollWait _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | seccompInstall _ _ _ _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | seccompProbe _ _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | seccompPrctl _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | seccompCapdrop =>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))
  | seccompQuery _ _ _=>exact fixed (fun _=>HolderOuter.dispatch_ordinary _ (by trivial))

theorem syscall (call : Syscall) : PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscall call) := by
  rw [Configuration.syscallRx_factor]
  apply SyscallSource.preserves safe store
  · exact dispatch call
  · exact send
  · exact idle
  · exact fixed (fun _=>HolderOuter.route)
  · exact after_xmit
  · exact after_advance
  · exact fixed (fun _=>HolderOuter.cleanup)

/-- Actual normal syscall endpoints conserve the complete key ledger, with
no temporary key credit remaining outside the native peer and packet holders. -/
theorem syscall_keys (call : Syscall) :
    Preserves (fun w : World=>∃h,Inv h w) (Leanux.syscall call) := by
  apply (hoare_iff_run _ _ _).mpr
  rintro w result v ⟨h,entry⟩ run
  have post := (syscall call w h entry).choose_spec.2.2
  rw [(RxHistory.syscall_erases call) w h,run] at post
  exact ⟨_,post⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
