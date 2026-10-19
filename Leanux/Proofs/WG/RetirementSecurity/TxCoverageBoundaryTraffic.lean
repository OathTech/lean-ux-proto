import Leanux.Proofs.WG.RetirementSecurity.TxCoverageControls
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageOuterTraffic
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTraffic

/-! The existing physical inventory and resident coverage meet at native
traffic boundaries. These endpoint facts do not infer internal event order. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits

abbrev Inv (_ : List RxHistory.Event) (w : World) := TxCovered.Inv [] [] w.wg

theorem wg_store {w v : World} (same : wgStoreView v.wg=wgStoreView w.wg)
    (before : TxCovered.Inv [] [] w.wg) : TxCovered.Inv [] [] v.wg := ready_store same before

theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) a) :
    PrefixPreserves (fun _ w=>TxCovered.Inv [] [] w.wg) (fun _=>True) g := by
  intro w h before
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e=>trivial
  | ok out=>exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 before ((erases w h).symm.trans run)

theorem native {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (keeps : PrefixPreserves (fun _ w=>TxCovered.Inv [] [] w.wg) (fun _=>True) g) :
    Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have actual := (erases w []).trans run
  have post := (keeps w [] before).choose_spec.2.2
  rw [actual] at post
  exact post

theorem inject_native (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) (Env.inject family port msg tos ll dest) :=
  product_join (OccurrenceTraffic.inject_native family port msg tos ll dest)
    (TxCoverageOuterTraffic.inject_native family port msg tos ll dest)

theorem flood_native (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) (Env.flood count port family messages) :=
  product_join (OccurrenceTraffic.flood_native count port family messages)
    (TxCoverageOuterTraffic.flood_native count port family messages)

theorem batch_native (items : List Env.BatchItem) :
    Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) (Env.batch items) :=
  product_join (OccurrenceTraffic.batch_native items) (TxCoverageOuterTraffic.batch_native items)

end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Traffic

namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Deferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits

theorem original (call : EnvDeferredCall) :
    Preserves (fun w:World=>TxCovered.Inv [] [] w.wg) call.original :=
  product_join (OccurrenceDeferred.original call) (TxCoverageDeferred.original call)

theorem send : PrefixPreserves Traffic.Inv (fun _=>True) RxHistory.runSendWorkers :=
  Traffic.observed _ _ RxHistory.runSendWorkers_appends RxHistory.runSendWorkers_erases (original .sendAll)

theorem idle : PrefixPreserves Traffic.Inv (fun _=>True) RxHistory.idleTimers :=
  Traffic.observed _ _ RxHistory.idleTimers_appends RxHistory.idleTimers_erases (original .idle)

theorem afterXmit : PrefixPreserves Traffic.Inv (fun _=>True) RxHistory.afterXmit :=
  Traffic.observed _ _ RxHistory.afterXmit_appends RxHistory.afterXmit_erases (original .afterXmit)

theorem afterAdvance : PrefixPreserves Traffic.Inv (fun _=>True) RxHistory.afterAdvance :=
  Traffic.observed _ _ RxHistory.afterAdvance_appends RxHistory.afterAdvance_erases (original .afterAdvance)

end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Deferred
