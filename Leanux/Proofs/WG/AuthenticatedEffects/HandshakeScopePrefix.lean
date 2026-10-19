import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeBalance

/-! The lexical handshake token is tied to the callback at this occurrence.
The existing authenticated callback event is emitted before its body, including
when that body stops; no earlier same-peer callback is selected as a substitute. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem callback_scope_run (scopeRecord : CausalScope.Event Cause → E)
    (cause : Cause) (record : HandshakeCausal.Event → E)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix E α)
    (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (CausalScope.scope scopeRecord cause
      (HandshakeWorker.callback record kind pid body)) w a h =
      match runWGPrefix body w a
          (h ++ [scopeRecord (.entered ⟨h.length,cause⟩),record (.callback kind pid)]) with
      | (.error stop,history) => (.error stop,history)
      | (.ok result,history) => (.ok result,history ++ [scopeRecord (.exited h.length)]) := by
  rw [CausalScope.scope,CausalScope.withToken_run]
  simp only [HandshakeWorker.callback,runWGPrefix,runStatePrefix_bind,runStatePrefix_emit,
    List.append_assoc,List.singleton_append]
  rfl

theorem callback_scope_entry (scopeRecord : CausalScope.Event Cause → E)
    (cause : Cause) (record : HandshakeCausal.Event → E)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix E α)
    (appends : StateAppends body) (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix, (runWGPrefix (CausalScope.scope scopeRecord cause
      (HandshakeWorker.callback record kind pid body)) w a h).2 =
      h ++ scopeRecord (.entered ⟨h.length,cause⟩) :: record (.callback kind pid) :: suffix := by
  obtain ⟨suffix,history⟩ := appends w a
    (h ++ [scopeRecord (.entered ⟨h.length,cause⟩),record (.callback kind pid)])
  rw [callback_scope_run]
  cases run : runWGPrefix body w a
      (h ++ [scopeRecord (.entered ⟨h.length,cause⟩),record (.callback kind pid)]) with
  | mk result output =>
    change (runWGPrefix body w a _).2 = _ at history
    rw [run] at history
    change output = _ at history
    cases result with
    | error stop => exact ⟨suffix,by simpa only [List.append_assoc,List.cons_append,List.nil_append] using history⟩
    | ok result => exact ⟨suffix ++ [scopeRecord (.exited h.length)],by
        simp only [history,List.append_assoc,List.cons_append,List.nil_append]⟩

/-- The context seen at callback body entry is its freshly emitted occurrence
and is independent of older admissions for that peer. -/
theorem callback_scope_current (scopeRecord : CausalScope.Event Cause → E)
    (scopeDecode : E → Option (CausalScope.Event Cause))
    (inverse : ∀ event, scopeDecode (scopeRecord event) = some event)
    (cause : Cause) (record : HandshakeCausal.Event → E)
    (quiet : ∀ event, scopeDecode (record event) = none)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (h : List E)
    (before : List (CausalScope.Token Cause))
    (ready : CausalScope.stack (h.filterMap scopeDecode) = .ok before) :
    CausalScope.current scopeDecode
      (h ++ [scopeRecord (.entered ⟨h.length,cause⟩),record (.callback kind pid)]) =
      .ok (some ⟨h.length,cause⟩) := by
  have current := CausalScope.current_entered scopeRecord scopeDecode inverse h before ready
    (CausalScope.Token.mk h.length cause)
  simpa only [CausalScope.current,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    Option.toList_none,List.nil_append,List.append_nil] using current

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
