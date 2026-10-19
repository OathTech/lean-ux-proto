import Leanux.Proofs.WG.RetirementSecurity.TxDrainObligations

/-! The actual admission return decides the precise added ring obligation.
The reverse work carrier is still local; these source contracts distinguish
successful ring insertion from EPIPE's subsequent publication continuation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem admission_ring (physical : TxDisposition.LiveFrontier.Physical w)
    (device : w.dev=some d) (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a=.ok ((ret,v),b)) :
    txCryptItems v=if ret=0 then txCryptItems w++[items] else txCryptItems w := by
  have cell:TxRing.nativeCell w=some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
  obtain ⟨n,h,refines⟩:=physical d device
  have effect:=TxRing.enqueue_result pid items w v a b ret run
  rw [cell] at effect
  rcases effect with ⟨returned,after⟩ | ⟨returned,after⟩ | ⟨returned,after,_⟩
  · have room:=TxRing.enqueue_free pid items cell (returned ▸ run)
    have mapped:=congrArg (fun cell:Option (Nat×PtrRing (List SkbId))=>
      (cell.map fun pair=>pair.2.items).getD []) after
    have live:txCryptItems v=(d.encryptQueue.produce items).items := by
      simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def,
        Option.map_some,Option.getD_some] using mapped
    rw [ite_eq_left returned,live,TxDisposition.LiveFrontier.produced_items refines room]
    simp only [txCryptItems,device,Option.map_some,Option.getD_some]
  · have same:TxRing.nativeCell v=TxRing.nativeCell w := after.trans cell.symm
    have mapped:=congrArg (fun cell:Option (Nat×PtrRing (List SkbId))=>
      (cell.map fun pair=>pair.2.items).getD []) same
    have nonzero:ret≠0 := by rw [returned]; decide
    simpa only [ite_eq_right nonzero,txCryptItems,TxRing.nativeCell,
      Option.map_map,Function.comp_def] using mapped
  · have same:TxRing.nativeCell v=TxRing.nativeCell w := after.trans cell.symm
    have mapped:=congrArg (fun cell:Option (Nat×PtrRing (List SkbId))=>
      (cell.map fun pair=>pair.2.items).getD []) same
    have nonzero:ret≠0 := by rw [returned]; decide
    simpa only [ite_eq_right nonzero,txCryptItems,TxRing.nativeCell,
      Option.map_map,Function.comp_def] using mapped

/-- Successful enqueue publishes the actual batch as a live logical ring
entry. The physical ring premise is separately initialized by campaign 1. -/
theorem admitted_pending (physical : TxDisposition.LiveFrontier.Physical w)
    (device : w.dev=some d) (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a=.ok ((0,v),b)) :
    items∈txCryptItems v := by
  rw [admission_ring physical device pid items a b run]
  simp

end Leanux.Proofs.WG.RetirementSecurity.TxWork
