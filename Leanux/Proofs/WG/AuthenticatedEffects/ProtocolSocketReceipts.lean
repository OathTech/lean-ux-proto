import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! The protocol sender's receipts describe the actual native socket call and
the lexical context at that call. No context is assumed authenticated here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem socket_completed (record : Receipt Context → E) (context : Context) (args : Args)
    (w v : WGWorld) (a b : Ambient) (history : List E) (value : Int)
    (run : (args.action.run w).run a = .ok ((value,v),b)) :
    runWGPrefix (socket record context args) w a history =
      (.ok ((value,v),b),history ++ [record ⟨context,args,⟨value,w,v,a,b⟩⟩]) := by
  rw [socket,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

theorem socket_receipts (record : Receipt Context → E) (context : Context) (args : Args)
    (w : WGWorld) (a : Ambient) (history : List E) :
    ∃ suffix, (runWGPrefix (socket record context args) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ event ∈ suffix, ∃ receipt,
        event = record receipt ∧ receipt.Valid ∧ receipt.cause = context ∧ receipt.args = args := by
  rw [socket,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases run : (args.action.run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok result =>
    rcases result with ⟨⟨value,v⟩,b⟩
    refine ⟨[record ⟨context,args,⟨value,w,v,a,b⟩⟩],rfl,by simp,?_⟩
    intro event member
    simp only [List.mem_singleton] at member
    subst event
    exact ⟨⟨context,args,⟨value,w,v,a,b⟩⟩,rfl,run,rfl,rfl⟩

theorem observed_frame (ρ : E → Option F) (record : Receipt (CausalEffects.Context Cause) → E)
    (quiet : ∀ receipt, ρ (record receipt) = none)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) :
    StateHistoryFrame ρ (observed record scope pid bytes) := by
  intro w a h
  exact (congrArg Prod.snd (observed_ignored ρ record quiet scope pid bytes w a h)).symm

theorem buffer_history (Safe : List E → Prop)
    (step : {α : Type} → WG.M α → WGPrefix E α) (call : Args → WGPrefix E Int)
    (hs : ∀ {α} (action : WG.M α), Driver.StateHistorySafe Safe (step action))
    (hc : ∀ args, Driver.StateHistorySafe Safe (call args)) (pid : PeerId) (bytes : List UInt8) :
    Driver.StateHistorySafe Safe (bufferWith step call pid bytes) := by
  unfold bufferWith
  repeat' first
    | exact hs _
    | exact hc _
    | with_reducible exact Driver.History.state_pure _
    | with_reducible apply Driver.History.state_bind
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem observed_history (Safe : List E → Prop)
    (record : Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause))
    (append : ∀ h args run, Safe h → run.Valid args.action →
      Safe (h ++ [record ⟨CausalScope.current scope h,args,run⟩]))
    (pid : PeerId) (bytes : List UInt8) : Driver.StateHistorySafe Safe (observed record scope pid bytes) := by
  apply buffer_history Safe liftWGPrefix _ Driver.History.state_lift
  intro args w a h hi
  have observedRun := CausalEffects.atCurrent_run scope (fun context => socket record context args) w a h
  rw [socket,runWGPrefix_receiptWGObserved,runWGPrefix_lift] at observedRun
  simp only [runWGPrefix,runStatePrefix] at observedRun
  rw [observedRun]
  cases run : (args.action.run w).run a with
  | error err => exact ⟨[],(List.append_nil h).symm,hi,True.intro⟩
  | ok result =>
    rcases result with ⟨⟨value,v⟩,b⟩
    have good := append h args ⟨value,w,v,a,b⟩ hi run
    exact ⟨[record ⟨CausalScope.current scope h,args,⟨value,w,v,a,b⟩⟩],rfl,good,good⟩

theorem observed_appends (record : Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) :
    StateAppends (observed record scope pid bytes) := by
  intro w a h
  obtain ⟨suffix,grown,_,_⟩ := observed_history (fun _ => True) record scope
    (fun _ _ _ _ _ => True.intro) pid bytes w a h True.intro
  exact ⟨suffix,grown⟩

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
