import Leanux.Proofs.WG.RetirementSecurity.HolderDumpCallers
import Leanux.Proofs.WG.Queues.HolderDumpEntry

/-! Full and stepped dump syscalls retain exact key credit with the actual
socket cursor ledger. The socket wrappers keep their original fd guards,
autobind and bounded serialization behavior. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DurableHolders NetlinkDump

private theorem native (action : WG.M α)
    (keeps : Preserves (During holders fd carriers loans temporary) action) :
    Preserves (fun w : World=>During holders fd carriers loans temporary w.wg) (liftWG action) :=
  PublicationPoll.native_product _ _ keeps

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World=>During holders fd carriers loans temporary w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ entry=>entry)

private theorem fs (action : FS.M α) :
    Preserves (fun w : World=>During holders fd carriers loans temporary w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ entry=>entry)

theorem get_dispatch (holders : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World=>During holders 7 carriers loans temporary w.wg) (dispatch (.wgGet ref)) := by
  simp only [dispatch,netlinkRequest,socketCall,socketCallOn]
  simp (config:={zeta:=false}) only [skipCut,modifyAmbient]
  repeat' first
    | (allocation_release_lift_from WG.M; exact native _ (device holders ref))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from FS.M; exact fs _)
    | rx_retention_step

theorem receive_dispatch (holders : DurableHolders) :
    Preserves (fun w : World=>During holders DUMP_FD carriers loans temporary w.wg) (dispatch .wgGetRecv) := by
  simp only [dispatch,socketCallOn]
  simp (config:={zeta:=false}) only [skipCut,unsupported,modifyAmbient]
  repeat' first
    | (allocation_release_lift_from WG.M; exact native _ (receive holders DUMP_FD))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from FS.M; exact fs _)
    | rx_retention_step

theorem socket (fd : Nat) (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>During holders cursor carriers loans temporary w.wg) body) :
    Preserves (fun w : World=>During holders cursor carriers loans temporary w.wg) (socketCallOn fd body) := by
  unfold socketCallOn
  apply preserves_bind (fs (fdget fd))
  intro f
  split
  · exact preserves_pure _
  · exact preserves_bind keeps (fun ret=>preserves_bind (fs (fdput f)) (fun _=>preserves_pure ret))

theorem start_dispatch (holders : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World=>During holders DUMP_FD carriers loans temporary w.wg)
      (dispatch (.wgGetStart ref)) := by
  let P := fun w : World=>During holders DUMP_FD carriers loans temporary w.wg
  have tail : Preserves P (do
      liftWG (netlinkDumpStart DUMP_FD ref)
      skipCut allocCuts
      pure (0:Int) : Leanux.M Int) :=
    preserves_bind (native _ (start holders DUMP_FD ref)) (fun _=>
      preserves_bind (ambient (AmbientM.skipCut allocCuts)) (fun _=>preserves_pure 0))
  have getter : Hoare (liftWG (getNlSock DUMP_FD)) P
      (fun sock w=>P w ∧ sock=socketAt DUMP_FD w.wg) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w sock v entry run
    change Except.ok (socketAt DUMP_FD w.wg,w)=Except.ok (sock,v) at run
    cases run
    exact ⟨entry,rfl⟩
  simp only [dispatch]
  apply socket
  apply preserves_bind (ambient (AmbientM.skipCut allocCuts))
  intro _
  apply hoare_bind _ _ getter
  intro sock
  split
  · apply hoare_bind _ _ (productAmbient_spec
      (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)
      (fun w : World=>P w ∧ sock=socketAt DUMP_FD w.wg) (fun _ _ entry=>entry))
    intro _
    apply hoare_bind _ _ (show Hoare (liftWG (setNlSock DUMP_FD {sock with bound:=true}))
      (fun w : World=>P w ∧ sock=socketAt DUMP_FD w.wg) (fun _=>P) from by
      apply (hoare_iff_run _ _ _).mpr
      intro w result v entry run
      change Except.ok ((),{w with wg:=writeSocket DUMP_FD {sock with bound:=true} w.wg})=Except.ok (result,v) at run
      cases run
      obtain ⟨next,funded,stable⟩ := entry.1.1
      have same : activeCursor {sock with bound:=true}=activeCursor (socketAt DUMP_FD w.wg) := by
        change activeCursor sock=activeCursor (socketAt DUMP_FD w.wg)
        exact congrArg activeCursor entry.2
      exact ⟨⟨next,socket_write_funded funded stable DUMP_FD {sock with bound:=true} same⟩,
        socket_keys entry.1.2.1 _ _,socket_anchors entry.1.2.2 _ _⟩)
    intro _
    exact tail
  · exact hoare_consequence tail (fun _ entry=>entry.1) (fun _ _ entry=>entry)

theorem initial (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w) (fd : Nat) :
    During holders fd carriers loans temporary w :=
  ⟨duringDump_initial holders fd funded stable,keys,anchors⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderDump

namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem dump_dispatch (call : Syscall) (fd : Nat)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.syscallDispatch call))
    (keeps : ∀holders,Preserves
      (fun w : World=>HolderDump.During holders fd carriers loans temporary w.wg) (dispatch call)) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := owner w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.syscallDispatch call) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have actual := ((RxHistory.syscallDispatch_erases call) w h).symm.trans run
    obtain ⟨holders,funded,stable⟩ := entry.1.1.1.1
    have anchors := KeySlotLiveness.references entry.2.2.2.2 funded entry.2.2.2.1 entry.1.1.1.2.2
    have after := (hoare_iff_run _ _ _).mp (keeps holders) w out.1 out.2
      (HolderDump.initial funded stable entry.2.1 anchors fd) actual
    exact ⟨post,after.2.1,(hoare_iff_run _ _ _).mp (OccurrenceSyscall.dispatch_native call)
        w out.1 out.2 entry.2.2.1 actual,
      post.1.1.2.1,(hoare_iff_run _ _ _).mp (KeySlotSyscall.dispatch_native call)
        w out.1 out.2 entry.2.2.2.2 actual⟩

theorem dump_get (ref : DeviceRef) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgGet ref)) :=
  dump_dispatch _ 7 (HolderDumpEntry.dispatchGet ref) (fun holders=>HolderDump.get_dispatch holders ref)

theorem dump_start (ref : DeviceRef) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgGetStart ref)) :=
  dump_dispatch _ DUMP_FD (HolderDumpEntry.dispatchStart ref) (fun holders=>HolderDump.start_dispatch holders ref)

theorem dump_receive : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgGetRecv) :=
  dump_dispatch _ DUMP_FD HolderDumpEntry.dispatchRecv HolderDump.receive_dispatch

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
