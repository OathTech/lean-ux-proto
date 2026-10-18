import Leanux.Proofs.WG.Index.ReachedDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedDeferred
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem entry_normal {α : Type} {action : RxHistory.Obs α}
    (keeps : ∀ initial loans before,PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe action)
    (absent : ∀ initial before,PrefixPreserves
      (fun h w=>productStoreView w=initial ∧ w.wg.dev=none ∧ h=before) (fun _=>True) action)
    {cs : Ledger} {loans : Reservations} {w v : World}
    {h k : List RxHistory.Event} {result : α}
    (pre : Reached.Entry cs loans h w)
    (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  cases device:w.wg.dev with
  | some d =>
    have post := (keeps cs loans h w h
      (Reached.entry_to_aux pre (by simp only [device,Option.isSome_some]))).choose_spec.2.2
    rw [run] at post
    exact Reached.aux_to_entry post
  | none =>
    have post := (absent (productStoreView w) h w h ⟨rfl,device,rfl⟩).choose_spec.2.2
    rw [run] at post
    have history : k=h := post.2.2
    have kept := Reached.entry_store post.1 pre
    have empty : remaining cs (NapiCarrier.removedPackets [])=cs :=
      List.filter_eq_self.mpr (fun _ _=>rfl)
    refine ⟨[],by simpa only [List.append_nil] using history,?_⟩
    simpa only [empty,history] using kept

theorem entry_checked {α : Type} {action : RxHistory.Obs α}
    (keeps : ∀ initial loans before,PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe action)
    (absent : ∀ initial before,PrefixPreserves
      (fun h w=>productStoreView w=initial ∧ w.wg.dev=none ∧ h=before) (fun _=>True) action)
    (owner : OwnerChecks.Preserves action)
    (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe action
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) := by
  intro w h pre
  obtain ⟨rfl,pre⟩ := pre
  obtain ⟨suffix,history,safe,_⟩ := owner w h pre.1.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out => exact entry_normal keeps absent pre (Prod.ext run rfl)

theorem entry_sendAll (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe RxHistory.runSendWorkers
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked sendAll
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_send))
    OwnerDeferred.runSendWorkers cs loans before

theorem entry_afterXmit (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe RxHistory.afterXmit
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked afterXmit
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_xmit))
    OwnerDeferred.afterXmit cs loans before

theorem entry_timers (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) (j : UInt64) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe (RxHistory.runTimers j)
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked (fun initial loans before=>timers initial loans before j)
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_timers) j)
    (OwnerDeferred.runTimers j) cs loans before

theorem entry_placeholder (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) (j : UInt64) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe (RxHistory.runTimersPlaceholder j)
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked (fun initial loans before=>placeholder initial loans before j)
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_placeholder) j)
    (OwnerDeferred.runTimersPlaceholder j) cs loans before

theorem entry_idle (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe RxHistory.idleTimers
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked idle
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_idle))
    OwnerDeferred.idleTimers cs loans before

theorem entry_afterAdvance (cs : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixEnsures (fun h w=>h=before ∧ Reached.Entry cs loans h w) OwnerChecks.Safe RxHistory.afterAdvance
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        Reached.Entry (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  entry_checked afterAdvance
    (fun _ _=>(pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred.absent_afterAdvance))
    OwnerDeferred.afterAdvance cs loans before

end Leanux.Proofs.WG.Index.ReachedDeferred
