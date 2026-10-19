import Leanux.Proofs.WG.TimerDiscipline.HookDeferredAtomsSource

/-! Existing deferred factories execute the actual scheduler/send callbacks.
Every contract remains conditional on those callbacks; this module introduces
no new operational traversal or initialized-run headline. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookDeferred
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open HookScheduler
variable {E : Type}

def crypt (c : Callbacks E) : PrefixM E Unit :=
  RxHistory.DeferredSource.cryptWith (HookScheduler.schedule c none)

def sendAll (c : Callbacks E) (sendOne : PrefixM E Unit) : PrefixM E Unit :=
  Noise.DriverTags.Deferred.sendWith (hooks sendOne) (HookScheduler.schedule c none)

def afterXmit (c : Callbacks E) (sendOne : PrefixM E Unit) : PrefixM E Unit :=
  RxHistory.DeferredSource.afterXmitWith (fun {_} a=>HookScheduler.old a)
    (crypt c) (sendAll c sendOne)

def timers (c : Callbacks E) (sendOne : PrefixM E Unit) (j : UInt64) : PrefixM E Bool :=
  Noise.DriverTags.Deferred.timersWith (fun {_} a=>HookScheduler.old a)
    (hooks sendOne) (crypt c) j

def placeholder (c : Callbacks E) (sendOne : PrefixM E Unit) (j : UInt64) : PrefixM E Unit :=
  Noise.DriverTags.Deferred.placeholderWith (fun {_} a=>HookScheduler.old a)
    (hooks sendOne) (crypt c) (sendAll c sendOne) j

def idle (c : Callbacks E) (sendOne : PrefixM E Unit) : PrefixM E Unit :=
  RxHistory.DeferredSource.idleWith (fun {_} a=>HookScheduler.old a)
    (timers c sendOne) (placeholder c sendOne)

def afterAdvance (c : Callbacks E) (sendOne : PrefixM E Unit) : PrefixM E Unit :=
  RxHistory.DeferredSource.afterAdvanceWith (fun {_} a=>HookScheduler.old a)
    (timers c sendOne) (placeholder c sendOne)

def observed (c : Callbacks E) (sendOne : PrefixM E Unit) (call : EnvDeferredCall) :
    PrefixM E call.Result :=
  Noise.DriverTags.Deferred.deferredWith (fun {_} a=>HookScheduler.old a)
    (hooks sendOne) (crypt c) (sendAll c sendOne) (afterXmit c sendOne)
    (timers c sendOne) (placeholder c sendOne) (idle c sendOne) (afterAdvance c sendOne) call

theorem crypt_erases (c : Callbacks E) (h : ErasureContracts c) :
    ErasesPrefix (crypt c) Env.runCryptWorkers :=
  Noise.DriverTags.Deferred.crypt_erases _ (HookScheduler.schedule_erases c h none)

theorem sendAll_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) :
    ErasesPrefix (sendAll c sendOne) Env.runSendWorkers :=
  Noise.DriverTags.Deferred.send_erases _ (hooks_erases sendOne hs) _
    (HookScheduler.schedule_erases c h none)

theorem afterXmit_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) :
    ErasesPrefix (afterXmit c sendOne) Env.afterXmit :=
  Noise.DriverTags.Deferred.afterXmit_erases _ quiet_erases _ _
    (crypt_erases c h) (sendAll_erases c h sendOne hs)

theorem timers_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) (j : UInt64) :
    ErasesPrefix (timers c sendOne j) (Env.runTimers j) :=
  Noise.DriverTags.Deferred.timers_erases _ quiet_erases _ (hooks_erases sendOne hs) _
    (crypt_erases c h) j

theorem placeholder_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) (j : UInt64) :
    ErasesPrefix (placeholder c sendOne j) (Env.runTimersPlaceholder j) :=
  Noise.DriverTags.Deferred.placeholder_erases _ quiet_erases _ (hooks_erases sendOne hs) _ _
    (crypt_erases c h) (sendAll_erases c h sendOne hs) j

theorem idle_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) :
    ErasesPrefix (idle c sendOne) Env.idleTimers :=
  Noise.DriverTags.Deferred.idle_erases _ quiet_erases _ _
    (timers_erases c h sendOne hs) (placeholder_erases c h sendOne hs)

theorem afterAdvance_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker) :
    ErasesPrefix (afterAdvance c sendOne) Env.afterAdvance :=
  Noise.DriverTags.Deferred.afterAdvance_erases _ quiet_erases _ _
    (timers_erases c h sendOne hs) (placeholder_erases c h sendOne hs)

theorem observed_erases (c : Callbacks E) (h : ErasureContracts c)
    (sendOne : PrefixM E Unit) (hs : ErasesPrefix sendOne Env.runOneSendWorker)
    (call : EnvDeferredCall) : ErasesPrefix (observed c sendOne call) call.original :=
  Noise.DriverTags.Deferred.deferred_erases _ quiet_erases _ (hooks_erases sendOne hs)
    _ _ _ _ _ _ _ (crypt_erases c h) (sendAll_erases c h sendOne hs)
    (afterXmit_erases c h sendOne hs) (timers_erases c h sendOne hs)
    (placeholder_erases c h sendOne hs) (idle_erases c h sendOne hs)
    (afterAdvance_erases c h sendOne hs) call

theorem crypt_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    PrefixPreserves (fun h _=>S h) S (crypt c) :=
  RxHistory.DeferredSource.crypt_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (HookScheduler.schedule_preserves S c h none)

theorem sendAll_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) :
    PrefixPreserves (fun h _=>S h) S (sendAll c sendOne) :=
  Noise.DriverTags.Deferred.send_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (hooks_preserves S sendOne hs) _
      (HookScheduler.schedule_preserves S c h none)

theorem afterXmit_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) :
    PrefixPreserves (fun h _=>S h) S (afterXmit c sendOne) :=
  Noise.DriverTags.Deferred.afterXmit_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (quiet_atoms S) _ _
      (crypt_preserves S c h) (sendAll_preserves S c h sendOne hs)

theorem timers_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) (j : UInt64) :
    PrefixPreserves (fun h _=>S h) S (timers c sendOne j) :=
  Noise.DriverTags.Deferred.timers_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (quiet_atoms S) _
      (hooks_preserves S sendOne hs) _ (crypt_preserves S c h) j

theorem placeholder_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) (j : UInt64) :
    PrefixPreserves (fun h _=>S h) S (placeholder c sendOne j) :=
  Noise.DriverTags.Deferred.placeholder_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (quiet_atoms S) _
      (hooks_preserves S sendOne hs) _ _ (crypt_preserves S c h)
      (sendAll_preserves S c h sendOne hs) j

theorem idle_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) :
    PrefixPreserves (fun h _=>S h) S (idle c sendOne) :=
  Noise.DriverTags.Deferred.idle_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (quiet_atoms S) _ _
      (timers_preserves S c h sendOne hs) (placeholder_preserves S c h sendOne hs)

theorem afterAdvance_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne) :
    PrefixPreserves (fun h _=>S h) S (afterAdvance c sendOne) :=
  Noise.DriverTags.Deferred.afterAdvance_preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre) _ (quiet_atoms S) _ _
      (timers_preserves S c h sendOne hs) (placeholder_preserves S c h sendOne hs)

theorem observed_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (sendOne : PrefixM E Unit) (hs : PrefixPreserves (fun h _=>S h) S sendOne)
    (call : EnvDeferredCall) : PrefixPreserves (fun h _=>S h) S (observed c sendOne call) :=
  Noise.DriverTags.Deferred.deferred_preserves _ (quiet_atoms S) _ (hooks_preserves S sendOne hs)
    _ _ _ _ _ _ _ (crypt_preserves S c h) (sendAll_preserves S c h sendOne hs)
    (afterXmit_preserves S c h sendOne hs) (timers_preserves S c h sendOne hs)
    (placeholder_preserves S c h sendOne hs) (idle_preserves S c h sendOne hs)
    (afterAdvance_preserves S c h sendOne hs) call

/-- The append contracts use existing trivial-safety preservation, without
another induction over any deferred loop. -/
theorem crypt_appends (c : Callbacks E) (h : AppendContracts c) :
    Appends (crypt c) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (crypt_preserves (fun _=>True) c (HookScheduler.append_history c h))

theorem sendAll_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) :
    Appends (sendAll c sendOne) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (sendAll_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs))

theorem afterXmit_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) :
    Appends (afterXmit c sendOne) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (afterXmit_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs))

theorem timers_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) (j : UInt64) :
    Appends (timers c sendOne j) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (timers_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs) j)

theorem placeholder_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) (j : UInt64) :
    Appends (placeholder c sendOne j) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (placeholder_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs) j)

theorem idle_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) :
    Appends (idle c sendOne) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (idle_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs))

theorem afterAdvance_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) :
    Appends (afterAdvance c sendOne) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (afterAdvance_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs))

theorem observed_appends (c : Callbacks E) (h : AppendContracts c)
    (sendOne : PrefixM E Unit) (hs : Appends sendOne) (call : EnvDeferredCall) :
    Appends (observed c sendOne call) := by
  let iffAppends : ∀ {α : Type} (action : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) action ↔ Appends action :=
    fun action => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) action
  exact (iffAppends _).mp (observed_preserves (fun _=>True) c (HookScheduler.append_history c h) sendOne
      ((iffAppends _).mpr hs) call)

end Leanux.Proofs.WG.TimerDiscipline.HookDeferred
