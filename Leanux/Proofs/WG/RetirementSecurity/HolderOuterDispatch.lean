import Leanux.Proofs.WG.RetirementSecurity.HolderDispatchQuiet

/-! Poll-free dispatch contracts join original peer-account observers with
native key conservation. All side conditions are derived at the actual source
entry; physical and slot-liveness facts use the same returned execution. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem checked (call : Syscall)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.syscallDispatch call))
    (keys : ∀{w h result v},Inv carriers loans temporary [] [] h w→
      (dispatch call).run w=.ok (result,v)→HolderAccount temporary v.wg) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := owner w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.syscallDispatch call) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have actual := ((RxHistory.syscallDispatch_erases call) w h).symm.trans run
    exact ⟨post,keys entry actual,(hoare_iff_run _ _ _).mp (OccurrenceSyscall.dispatch_native call)
      w out.1 out.2 entry.2.2.1 actual,post.1.1.2.1,
      (hoare_iff_run _ _ _).mp (KeySlotSyscall.dispatch_native call) w out.1 out.2 entry.2.2.2.2 actual⟩

theorem checked_keys (call : Syscall)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.syscallDispatch call))
    (keeps : Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch call)) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch call) :=
  checked call owner (fun entry run=>(hoare_iff_run _ _ _).mp keeps _ _ _ entry.2.1 run)

theorem checked_boundary (call : Syscall)
    (owner : PrefixPreserves (HolderEntry.Inv carriers loans) OwnerChecks.Safe (RxHistory.syscallDispatch call))
    (keeps : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (dispatch call)) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch call) :=
  checked call owner (fun entry run=>((hoare_iff_run _ _ _).mp keeps _ _ _
    (HolderBoundary.of_owner entry.2.1 entry.1 entry.2.2.2.2) run).1.1)

theorem dispatch_configure (attrs : DeviceAttrs) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) :=
  checked_boundary _ (HolderEntryPollFree.configuration attrs) (HolderDispatch.configuration attrs)

theorem dispatch_up : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch .wgUp) :=
  checked_boundary _ HolderEntryPollFree.up HolderDispatch.up

theorem dispatch_down : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch .wgDown) :=
  checked_boundary _ HolderEntryPollFree.down HolderDispatch.down

theorem dispatch_create : PrefixPreserves (Inv carriers loans [] [] []) OwnerChecks.Safe (RxHistory.syscallDispatch .wgCreate) :=
  checked_keys _ HolderEntryPollFree.create HolderDispatch.create

theorem dispatch_delete : PrefixPreserves (Inv carriers [] [] [] []) OwnerChecks.Safe (RxHistory.syscallDispatch .wgDelete) :=
  checked _ HolderEntryPollFree.delete (fun entry run=>
    ((hoare_iff_run _ _ _).mp HolderDispatch.delete _ _ _ ⟨entry.1.1,entry.2.1⟩ run).2)

theorem dispatch_mtu (n : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgSetMtu n)) :=
  checked_keys _ (HolderEntryPollFree.mtu n) (HolderDispatch.mtu n)

theorem dispatch_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) :=
  checked _ (HolderEntryDispatch.xmit family addr payload opts) (fun entry run=>
    ((hoare_iff_run _ _ _).mp (HolderDispatch.xmit family addr payload opts) _ _ _
      ⟨entry.2.1,entry.2.2.1.1,entry.1.1.2.2⟩ run).1)

theorem dispatch_deladdr (family : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgDeladdr family)) :=
  checked_keys _ (HolderEntryPollFree.deladdr family) (HolderDispatch.deladdr family)

theorem dispatch_delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgDelroute family named dst plen oif typeCode metric)) :=
  checked_keys _ (HolderEntryPollFree.delroute family named dst plen oif typeCode metric)
    (HolderDispatch.delroute family named dst plen oif typeCode metric)

theorem dispatch_addroute (dst plen oif typeCode metric mtu flags : Nat) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgAddroute dst plen oif typeCode metric mtu flags)) :=
  checked_keys _ (HolderEntryPollFree.addroute dst plen oif typeCode metric mtu flags)
    (HolderDispatch.addroute dst plen oif typeCode metric mtu flags)

theorem dispatch_addaddr (addr plen : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAddaddr addr plen)) :=
  checked_keys _ (HolderEntryPollFree.addaddr addr plen) (HolderDispatch.addaddr addr plen)

theorem dispatch_advance (ticks : Nat) : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAdvance ticks)) :=
  checked_keys _ (HolderEntryPollFree.advance ticks) (HolderDispatch.advance ticks)

theorem dispatch_namespace : PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgNetnsClose) :=
  checked_keys _ HolderEntryPollFree.namespaceClose HolderDispatch.namespace_close

theorem dispatch_ordinary (call : Syscall) (selected : HolderEntryPollFree.Ordinary call) :
    PrefixPreserves (Inv carriers loans temporary [] []) OwnerChecks.Safe (RxHistory.syscallDispatch call) :=
  checked_keys _ (HolderEntryPollFree.ordinary call selected) (HolderDispatch.ordinary call selected)

end Leanux.Proofs.WG.RetirementSecurity.HolderOuter
