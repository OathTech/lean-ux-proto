import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketSource

/-! Protocol socket instrumentation preserves the complete old journal, state,
result, and stopped prefix. Native erasure alone is not used to join histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem buffer_projects (ρ : E → Option F)
    (sg : {α : Type} → WG.M α → WGPrefix E α)
    (st : {α : Type} → WG.M α → WGPrefix F α)
    (cg : Args → WGPrefix E Int) (ct : Args → WGPrefix F Int)
    (step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (sg action) (st action))
    (call : ∀ args, StateProjectsPrefix ρ id (cg args) (ct args))
    (pid : PeerId) (bytes : List UInt8) :
    StateProjectsPrefix ρ id (bufferWith sg cg pid bytes) (bufferWith st ct pid bytes) := by
  unfold bufferWith
  repeat' first
    | exact step _
    | exact call _
    | handshake_worker_project_step ρ

theorem buffer_erases
    (step : {α : Type} → WG.M α → WGPrefix E α)
    (call : Args → WGPrefix E Int)
    (hs : ∀ {α} (action : WG.M α), ErasesStatePrefix (step action) action)
    (hc : ∀ args, ErasesStatePrefix (call args) args.action)
    (pid : PeerId) (bytes : List UInt8) :
    ErasesStatePrefix (bufferWith step call pid bytes) (sendBufferToPeer pid bytes) := by
  rw [← buffer_factor]
  unfold bufferWith
  repeat' first
    | exact hs _
    | exact hc _
    | work_root_erasure_step

theorem buffer_frame (ρ : E → Option F)
    (step : {α : Type} → WG.M α → WGPrefix E α)
    (call : Args → WGPrefix E Int)
    (hs : ∀ {α} (action : WG.M α), StateHistoryFrame ρ (step action))
    (hc : ∀ args, StateHistoryFrame ρ (call args))
    (pid : PeerId) (bytes : List UInt8) :
    StateHistoryFrame ρ (bufferWith step call pid bytes) := by
  unfold bufferWith
  repeat' first
    | exact hs _
    | exact hc _
    | (change StateHistoryFrame ρ (pure _); exact fun _ _ _ => rfl)
    | with_reducible apply StateHistoryFrame.bind
    | contradiction
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem buffer_lifted (pid : PeerId) (bytes : List UInt8) :
    bufferWith (m := WGPrefix E) liftWGPrefix (fun args => liftWGPrefix args.action) pid bytes =
      (liftWGPrefix (sendBufferToPeer pid bytes) : WGPrefix E Unit) :=
  TimerEffects.eq_native_lift
    (buffer_erases liftWGPrefix _ erasesStatePrefix_lift (fun _ => erasesStatePrefix_lift _) pid bytes)
    (buffer_frame some liftWGPrefix _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) pid bytes)

theorem socket_erases (record : Receipt Context → E) (context : Context) (args : Args) :
    ErasesStatePrefix (socket record context args) args.action :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem socket_ignored (ρ : E → Option F) (record : Receipt Context → E)
    (quiet : ∀ receipt, ρ (record receipt) = none) (context : Context) (args : Args) :
    StateProjectsPrefix ρ id (socket record context args) (liftWGPrefix args.action) := by
  intro w a h
  change ((args.action.run w).run a,h.filterMap ρ) =
    ((runWGPrefix (socket record context args) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (socket record context args) w a h).2.filterMap ρ)
  rw [socket,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases result : (args.action.run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    simp only [Except.map,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      quiet,List.append_nil]

theorem observed_erases (record : Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) :
    ErasesStatePrefix (observed record scope pid bytes) (sendBufferToPeer pid bytes) :=
  buffer_erases liftWGPrefix _ erasesStatePrefix_lift
    (fun args => CausalEffects.atCurrent_erases scope _ _ (fun context => socket_erases record context args)) pid bytes

theorem observed_ignored (ρ : E → Option F) (record : Receipt (CausalEffects.Context Cause) → E)
    (quiet : ∀ receipt, ρ (record receipt) = none)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) :
    StateProjectsPrefix ρ id (observed record scope pid bytes)
      (liftWGPrefix (sendBufferToPeer pid bytes)) := by
  rw [← buffer_lifted]
  apply buffer_projects ρ
  · intro α action w a h
    change ((action.run w).run a,h.filterMap ρ) =
      (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
    cases (action.run w).run a <;> rfl
  · intro args
    exact CausalEffects.atCurrent_projects scope _ ρ _
      (fun context => socket_ignored ρ record quiet context args)

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
