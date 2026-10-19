import Leanux.Proofs.WG.RetirementSecurity.HolderOuterDispatch
import Leanux.Proofs.WG.RetirementSecurity.HolderDumpDispatch
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant

/-! The original source observer transports the joint key account with its
actual residual receive ledger. Existential selection hides only that derived
ledger, never an incoming funding or source-coverage premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  ∃carriers,HolderOuter.Inv carriers [] [] [] [] h w

theorem safe (_h : List RxHistory.Event) (_w : World) (entry : Inv _h _w) : OwnerChecks.Safe _h :=
  entry.choose_spec.1.2.safe

theorem store (_h : List RxHistory.Event) (_w _v : World)
    (same : wgStoreView _v.wg=wgStoreView _w.wg) (entry : Inv _h _w) : Inv _h _v :=
  ⟨entry.choose,HolderEntryDispatch.wg_store entry.choose_spec.1 same,
    HolderScheduled.extra_wg_store entry.choose_spec.2 same⟩

theorem fixed {action : RxHistory.Obs α}
    (keeps : ∀carriers,PrefixPreserves (HolderOuter.Inv carriers [] [] [] []) OwnerChecks.Safe action) :
    PrefixPreserves Inv OwnerChecks.Safe action := by
  rintro w h ⟨carriers,entry⟩
  obtain ⟨suffix,history,safe,post⟩ := keeps carriers w h entry
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error e=>trivial
  | ok out=>rw [run] at post; exact ⟨carriers,post⟩

theorem normal {action : RxHistory.Obs α} (owner : OwnerChecks.Preserves action)
    (keeps : ∀{w h result v k},Inv h w→runPrefix action w h=(.ok (result,v),k)→Inv k v) :
    PrefixPreserves Inv OwnerChecks.Safe action := by
  intro w h entry
  obtain ⟨suffix,history,safe,_⟩ := owner w h entry.choose_spec.1.2
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix action w h).1 with
  | error e=>trivial
  | ok out=>exact keeps entry (Prod.ext run rfl)

theorem lift_wg (action : Leanux.M α)
    (frame : SameView (fun w : World=>wgStoreView w.wg) action) :
    PrefixPreserves Inv OwnerChecks.Safe (liftPrefix action) :=
  viewLiftPrefix_preserves (fun w : World=>wgStoreView w.wg) safe store frame

theorem send : PrefixPreserves Inv OwnerChecks.Safe RxHistory.runSendWorkers :=
  normal OwnerDeferred.runSendWorkers (fun entry run=>by
    obtain ⟨_,_,post⟩ := HolderOuter.send_normal entry.choose_spec run
    exact ⟨_,post⟩)

theorem idle : PrefixPreserves Inv OwnerChecks.Safe RxHistory.idleTimers :=
  normal OwnerDeferred.idleTimers (fun entry run=>by
    obtain ⟨_,_,post⟩ := HolderOuter.idle_normal entry.choose_spec run
    exact ⟨_,post⟩)

theorem after_xmit : PrefixPreserves Inv OwnerChecks.Safe RxHistory.afterXmit :=
  normal OwnerDeferred.afterXmit (fun entry run=>by
    obtain ⟨_,_,post⟩ := HolderOuter.after_xmit_normal entry.choose_spec run
    exact ⟨_,post⟩)

theorem after_advance : PrefixPreserves Inv OwnerChecks.Safe RxHistory.afterAdvance :=
  normal OwnerDeferred.afterAdvance (fun entry run=>by
    obtain ⟨_,_,post⟩ := HolderOuter.after_advance_normal entry.choose_spec run
    exact ⟨_,post⟩)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.inject family port msg tos ll dest) :=
  normal (OwnerTraffic.inject family port msg tos ll dest) (fun entry run=>
    ⟨[],HolderOuter.inject_normal entry.choose_spec run⟩)

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.flood count port family messages) :=
  normal (OwnerTraffic.flood count port family messages) (fun entry run=>by
    obtain ⟨next,_,post⟩ := HolderOuter.flood_normal entry.choose_spec run
    exact ⟨next,post⟩)

theorem batch (items : List BatchItem) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.batch items) :=
  normal (OwnerTraffic.batch items) (fun entry run=>by
    obtain ⟨next,_,post⟩ := HolderOuter.batch_normal items entry.choose_spec run
    exact ⟨next,post⟩)

theorem socket (fd : Nat) (body : RxHistory.Obs Int)
    (keeps : PrefixPreserves Inv OwnerChecks.Safe body) :
    PrefixPreserves Inv OwnerChecks.Safe (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  apply PrefixPreserves.bind (lift_wg _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ hi=>hi)))
  intro f
  split
  · exact PrefixPreserves.pure safe _
  · exact PrefixPreserves.bind keeps (fun ret=>PrefixPreserves.bind
      (lift_wg _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ hi=>hi)))
      (fun _=>PrefixPreserves.pure safe ret))

theorem observe : PrefixPreserves Inv OwnerChecks.Safe RxHistory.observe :=
  PrefixPreserves.bind idle (fun _=>lift_wg _
    (observeTail_sameKernel.of_factor (fun s : ProductStore43=>s.2.2.2) _ (fun _=>rfl)))

theorem observe_dispatch : PrefixPreserves Inv OwnerChecks.Safe (RxHistory.syscallDispatch .wgObserve) := by
  unfold RxHistory.syscallDispatch
  apply PrefixPreserves.bind observe
  intro out
  apply PrefixPreserves.bind
  · apply lift_wg
    intro initial
    exact productAmbient_spec _ _ (fun _ _ hi=>hi)
  · intro _
    exact socket _ _ (PrefixPreserves.pure safe _)

end Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
