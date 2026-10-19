import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredOuter

/-! Native normal returns choose the history produced by the original
observer itself. Existential outer hiding happens after the exact residual
carrier/account pair has been established on that one returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Deferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders

/-- Preserve the source history relation before hiding it at outer calls. -/
theorem native {action : RxHistory.Obs α} {original : Leanux.M α}
    (erase : ErasesPrefix action original)
    (endpoint : ∀ {w v k result}, Inv cs loans h w →
      runPrefix action w h=(.ok (result,v),k) →
      ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v)
    (hi : Inv cs loans h w) (run : original.run w=.ok (result,v)) :
    let k := (runPrefix action w h).2
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  endpoint hi (Prod.ext ((erase w h).trans run) rfl)

theorem sendAll_native (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : Env.runSendWorkers.run w=.ok ((),v)) :
    let k := (runPrefix RxHistory.runSendWorkers w h).2
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  native RxHistory.runSendWorkers_erases (sendAll_normal crypt) hi run

theorem idle_native (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : Env.idleTimers.run w=.ok ((),v)) :
    let k := (runPrefix RxHistory.idleTimers w h).2
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  native RxHistory.idleTimers_erases (idle_normal crypt) hi run

theorem afterXmit_native (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : Env.afterXmit.run w=.ok ((),v)) :
    let k := (runPrefix RxHistory.afterXmit w h).2
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  native RxHistory.afterXmit_erases (afterXmit_normal crypt) hi run

theorem afterAdvance_native (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : Env.afterAdvance.run w=.ok ((),v)) :
    let k := (runPrefix RxHistory.afterAdvance w h).2
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  native RxHistory.afterAdvance_erases (afterAdvance_normal crypt) hi run

private theorem hide {action : RxHistory.Obs α} {original : Leanux.M α}
    (erase : ErasesPrefix action original)
    (endpoint : ∀ cs h, ∀ {w v k result}, Inv cs [] h w →
      runPrefix action w h=(.ok (result,v),k) →
      ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) [] k v) :
    Preserves Boundary original := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨h,cs,entry⟩ := hi
  obtain ⟨suffix,_,post⟩ := native erase (endpoint cs h) entry run
  exact ⟨(runPrefix action w h).2,remaining cs (NapiCarrier.removedPackets suffix),post⟩

theorem sendAll_boundary (crypt : ∀ cs h, Crypt cs [] h) :
    Preserves Boundary Env.runSendWorkers :=
  hide RxHistory.runSendWorkers_erases (fun cs h => sendAll_normal (crypt cs h))

theorem idle_boundary (crypt : ∀ cs h, Crypt cs [] h) :
    Preserves Boundary Env.idleTimers :=
  hide RxHistory.idleTimers_erases (fun cs h => idle_normal (crypt cs h))

theorem afterXmit_boundary (crypt : ∀ cs h, Crypt cs [] h) :
    Preserves Boundary Env.afterXmit :=
  hide RxHistory.afterXmit_erases (fun cs h => afterXmit_normal (crypt cs h))

theorem afterAdvance_boundary (crypt : ∀ cs h, Crypt cs [] h) :
    Preserves Boundary Env.afterAdvance :=
  hide RxHistory.afterAdvance_erases (fun cs h => afterAdvance_normal (crypt cs h))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Deferred
