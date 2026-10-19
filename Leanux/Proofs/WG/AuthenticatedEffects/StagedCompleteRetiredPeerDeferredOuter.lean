import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliaryEntry
import Leanux.Proofs.WG.Queues.HolderEntryDeferred

/-! Return-to-user waits preserve the paired outer entry at exactly the
native observer suffix. Present and absent device branches keep their own
source cases; no physical-ring premise is imposed on an absent device. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Deferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders

private theorem normal {action : RxHistory.Obs α}
    (account : PrefixPreserves (Auxiliary.Inv cs loans h) OwnerChecks.Safe action)
    (structural : ∀ initial,PrefixPreserves (fun _ w => BaseCoherence.view w.wg=initial) (fun _ => True) action)
    (absent : ∀ {w v h k result}, w.wg.dev=none →
      runPrefix action w h=(.ok (result,v),k) → productStoreView v=productStoreView w ∧ k=h)
    (hi : Inv cs loans h w) (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  cases dev : w.wg.dev with
  | some d => exact auxiliary_normal account structural hi (by simp only [dev,Option.isSome_some]) run
  | none =>
    obtain ⟨same,history⟩ := absent dev run
    have kept := Outer.store hi same
    have empty : remaining cs (NapiCarrier.removedPackets [])=cs :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    exact ⟨[],by simpa only [List.append_nil] using history,by simpa only [empty,history] using kept⟩

private theorem absent_idle (absent : w.wg.dev=none)
    (run : runPrefix RxHistory.idleTimers w h=(.ok (result,v),k)) :
    productStoreView v=productStoreView w ∧ k=h := by
  have source : PrefixPreserves
      (fun j u => productStoreView u=productStoreView w ∧ u.wg.dev=none ∧ j=h)
      (fun _ => True) RxHistory.idleTimers :=
    pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_idle
  have post := (source w h ⟨rfl,absent,rfl⟩).choose_spec.2.2
  rw [run] at post
  exact ⟨post.1,post.2.2⟩

private theorem absent_afterAdvance (absent : w.wg.dev=none)
    (run : runPrefix RxHistory.afterAdvance w h=(.ok (result,v),k)) :
    productStoreView v=productStoreView w ∧ k=h := by
  have source : PrefixPreserves
      (fun j u => productStoreView u=productStoreView w ∧ u.wg.dev=none ∧ j=h)
      (fun _ => True) RxHistory.afterAdvance :=
    pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_afterAdvance
  have post := (source w h ⟨rfl,absent,rfl⟩).choose_spec.2.2
  rw [run] at post
  exact ⟨post.1,post.2.2⟩

theorem sendAll_normal (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : runPrefix RxHistory.runSendWorkers w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  apply normal (RetiredPeer.Deferred.runSendWorkers crypt.actors) BaseCoherence.runSendWorkers_structure ?_ hi run
  intro w v h k result absent actual
  rw [HolderEntryDeferred.send_absent absent] at actual
  cases actual
  exact ⟨rfl,rfl⟩

theorem idle_normal (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : runPrefix RxHistory.idleTimers w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal (DeferredTimers.idleTimers cs loans h crypt.actors) BaseCoherence.idleTimers_structure
    absent_idle hi run

theorem afterXmit_normal (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : runPrefix RxHistory.afterXmit w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  apply normal (RetiredPeer.Deferred.afterXmit crypt.actors) BaseCoherence.afterXmit_structure ?_ hi run
  intro w v h k result absent actual
  rw [HolderEntryDeferred.xmit_absent absent] at actual
  cases actual
  exact ⟨rfl,rfl⟩

theorem afterAdvance_normal (crypt : Crypt cs loans h) (hi : Inv cs loans h w)
    (run : runPrefix RxHistory.afterAdvance w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal (DeferredTimers.afterAdvance cs loans h crypt.actors) BaseCoherence.afterAdvance_structure
    absent_afterAdvance hi run

private theorem checked {action : RxHistory.Obs α}
    (owner : OwnerChecks.Preserves action)
    (endpoint : ∀ {w v k result}, Inv cs loans before w →
      runPrefix action w before=(.ok (result,v),k) →
      ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :
    PrefixEnsures (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe action
      (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) := by
  intro w h hi
  rcases hi with ⟨rfl,hi⟩
  obtain ⟨suffix,history,safe,_⟩ := owner w h hi.1.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error reason => trivial
  | ok out => exact endpoint hi (Prod.ext run rfl)

theorem sendAll (crypt : Crypt cs loans before) : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.runSendWorkers
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.runSendWorkers (sendAll_normal crypt)

theorem idle (crypt : Crypt cs loans before) : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.idleTimers
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.idleTimers (idle_normal crypt)

theorem afterXmit (crypt : Crypt cs loans before) : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.afterXmit
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.afterXmit (afterXmit_normal crypt)

theorem afterAdvance (crypt : Crypt cs loans before) : PrefixEnsures
    (fun h w => h=before ∧ Inv cs loans h w) OwnerChecks.Safe RxHistory.afterAdvance
    (fun _ k v => ∃ suffix,k=before++suffix ∧ Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.afterAdvance (afterAdvance_normal crypt)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Deferred
