import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryNativeProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive

/-! Quiet-actor history frames paired with their exact native state results.
This surrogate is used only where the source does not invoke a replay check;
actual poll checks use the state-dependent entry contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Keypairs Lifetimes Driver
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def quietHooks : Driver.Hooks Event := { hooks with
  counterCheck := fun _ packet => liftWGObserver (liftWGPrefix (counterValidate packet.keypair packet.nonce)) }

open Lean Meta Elab Tactic in
elab "replay_callback " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size > 0 do throwError "no observed body"
  let action := args.back!.consumeMData.headBeta
  let .fvar fn := action.getAppFn | throwError "not a supplied callback"
  let decl ← fn.getDecl
  unless decl.userName == wanted.getId do throwError "different callback"

theorem source_history (Good : List E → Prop)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Good (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Good (keepalive pid)) :
    Driver.StateHistorySafe Good (HandshakeWorker.source session keepalive) := by
  unfold HandshakeWorker.source HandshakeWorker.workerWith
    Origins.HandshakeSources.receptionWith Origins.HandshakeSources.afterMacWith
    Origins.HandshakeSources.responseWith
  simp only [HandshakeWorker.ops]
  repeat' first
    | (replay_callback session; exact hs _)
    | (replay_callback keepalive; exact hk _)
    | driver_state_history_step

theorem quiet_history (Good : List Event → Prop) : Driver.HooksHistorySafe Good quietHooks := by
  constructor
  · intro pid packets; exact Driver.History.state_lift _
  · intro pid; exact Driver.History.state_lift _
  · intro peer; exact Driver.History.state_lift _
  · exact Driver.History.product_lift _
  · intro pid; exact Driver.History.state_lift _
  · intro trigger; exact Driver.History.state_pure _
  · intro token; exact Driver.History.state_pure _
  · exact source_history Good
  all_goals intros
  all_goals first
    | assumption
    | (rw [Driver.sendWorker_lift quietHooks rfl]; exact Driver.History.product_lift _)
    | exact Driver.History.state_lift _
    | exact Driver.History.product_lift _
    | exact Driver.History.product_state (Driver.History.state_lift _)
    | exact Driver.History.product_pure _

theorem state_observed (body : WGPrefix Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native)
    (history : Driver.StateHistorySafe Safe body) (frame : OrdinaryAction native) : StateSafe body := by
  intro w a h hi
  obtain ⟨suffix,appended,safe,_⟩ := history w a h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix (body.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have nativeRun : (native.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans run
    have kept := ReplayRefusal.ordinary_coherent
      ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b nativeRun) hi.1
    simpa only [run,appended,Inv] using And.intro kept safe

theorem product_observed (body : PrefixM Event α) (native : Leanux.M α)
    (erases : ErasesPrefix body native)
    (history : Driver.ProductHistorySafe Safe body) (frame : ProductOrdinaryAction native) : ProductSafe body := by
  intro w h hi
  obtain ⟨suffix,appended,safe,_⟩ := history w h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix body w h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,v⟩
    have nativeRun : native.run w = .ok (value,v) := (erases w h).symm.trans run
    have kept := ReplayRefusal.ordinary_coherent
      ((ProjectedAction.iff_run _ _ _).mp frame w value v nativeRun) hi.1
    simpa only [run,appended,Inv] using And.intro kept safe

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) :=
  state_observed _ _ (staging_erases pid)
    (Driver.staging_history (quiet_history Safe) pid) (WGTransitions.sendStagedPackets_ordinary pid)

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) :=
  state_observed _ _ (keepalive_erases pid)
    (Driver.keepalive_history (quiet_history Safe) pid) (WGTransitions.sendKeepalive_ordinary pid)

theorem handshake : StateSafe (Driver.handshakeObserved hooks) := by
  apply state_observed _ _ handshake_erases _ SchedulerObservers.receiveStep_ordinary
  change Driver.StateHistorySafe Safe (Driver.handshakeObserved quietHooks)
  exact Driver.handshake_history (quiet_history Safe).core

theorem consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    StateSafe (Driver.consumeObserved hooks pid packet endpoint) :=
  state_observed _ _ (consume_erases pid packet endpoint)
    (Driver.consume_history (quiet_history Safe).core pid packet endpoint)
    (WGMore.consumeDataDone_ordinary pid packet endpoint)

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
