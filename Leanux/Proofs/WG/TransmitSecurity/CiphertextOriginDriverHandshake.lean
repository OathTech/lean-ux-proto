import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginDriverWorkers
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginHandshakeFrames

/-! The actual handshake journal preserves TX ciphertext certificates, including
the response-driven keepalive callback that can allocate new TX packets. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects Origins.HandshakeSources RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem state_emit (e : Journal.Event) (quiet : Journal.SocketHistory.socket? e = none) :
    StateSafe (emitStatePrefix e) := by
  have keep (h : List Journal.Event) (w : WGWorld) (_ : Ambient) (hi : JournalInv h w) :
      JournalInv (h ++ [e]) w :=
    ⟨hi.1.mono (receipts_mono (fun _ member => List.mem_append_left _ member)),hi.2.quiet_suffix
      (by simp only [List.filterMap_cons,List.filterMap_nil,quiet])⟩
  exact StatePrefixEnsures.emit e (fun h w a hi => (keep h w a hi).2) keep

theorem handshake_focus (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erase : ErasesStatePrefix body native) (keeps : ∀ h, Preserves (Inv h) native) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? body) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) (body.run w))
    (focusStatePrefix_erases _ _ erase) keeps

theorem handshake_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (keeps : ∀ h, Preserves (Inv h) native) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake?
      (HandshakeCausal.call kind pid native)) :=
  handshake_focus _ native (HandshakeCausal.call_erases kind pid native) keeps

theorem handshake_initiation (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.initiation mac)) :=
  handshake_focus _ _ (HandshakeCausal.initiation_erases mac)
    (fun _ => frame (snapshot_wire (OccurrenceHandshake.consume_initiation_wire mac.input)))

theorem handshake_response_read (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.response mac)) :=
  handshake_focus _ _ (HandshakeCausal.response_erases mac)
    (fun _ => frame (snapshot_wire (OccurrenceHandshake.consume_response_wire mac.input)))

theorem peer_update (pid : PeerId) (f : Peer → Peer) :
    Preserves (Inv h) (do setPeer pid (f (← getPeer pid))) :=
  preserves_bind (NativeFrames.read_peer pid) (fun _ => frame (CiphertextOrigins.modify _ (fun _ => rfl) (fun _ => rfl)))

theorem session (pid : PeerId) : StateSafe (Journal.session pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.Responder.DriverCuts.session pid).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.Responder.DriverCuts.session_erases pid))
    (fun _ => frame (snapshot_wire (OccurrenceKeys.session_wire pid)))

theorem capture (native : WG.M α) (keeps : ∀ h, Preserves (Inv h) native) :
    StateSafe (captureWGRun native) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.2)
  intro h w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (keeps (receipts h)) w a x v b hi.1 run,hi.2⟩

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Journal.Event α)
    (ha : StateSafe a) (hb : StateSafe b) : StateSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

open Lean Meta Elab Tactic in
elab "ciphertext_native_lift" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``StatePrefixPreserves then pure args.back!
    else if target.isAppOf ``StatePrefixEnsures then pure args[args.size - 2]!
    else throwError "not a state-prefix contract"
  unless action.consumeMData.headBeta.isAppOf ``liftWGPrefix do
    throwError "not a native lift"

open Lean Meta Elab Tactic in
elab "ciphertext_old_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``StatePrefixPreserves then pure args.back!
    else if target.isAppOf ``StatePrefixEnsures then pure args[args.size - 2]!
    else throwError "not a state-prefix contract"
  unless action.isAppOf ``HandshakeWorker.old do throwError "not an old handshake cut"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := body.getAppFn | throwError "not a constant-headed body"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different handshake cut"

macro "ciphertext_handshake_source" : tactic => `(tactic| first
  | (nonce_source_head pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi))
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _)
  | (nonce_source_head Journal.session; exact session _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (ciphertext_old_head HandshakeCausal.call
     apply handshake_call; intro h
     first | (rx_retention_head Bind.bind; exact peer_update _ _) | (repeat' ciphertext_handshake_frame; done))
  | (ciphertext_old_head HandshakeCausal.initiation; exact handshake_initiation _)
  | (ciphertext_old_head HandshakeCausal.response; exact handshake_response_read _)
  | (nonce_source_head emitStatePrefix; exact state_emit _ rfl)
  | (nonce_source_head captureWGRun
     apply capture; intro h; repeat' ciphertext_handshake_frame; done)
  | (ciphertext_native_lift; apply state_lift; intro h; repeat' ciphertext_handshake_frame
     all_goals first
       | done
       | (apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x v b hi run
          cases run
          exact hi))
  | ciphertext_driver_step)

theorem handshake_response (mac : HandshakeMac) (pid : PeerId) :
    StateSafe (responseWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' ciphertext_handshake_source

theorem handshake_after (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) msg src loaded state) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold afterMacWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response _ _)
    | ciphertext_handshake_source
  all_goals exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem handshake_receive (msg : Key) (src : SkbSource) :
    StateSafe (HandshakeWorker.observedReceive Journal.Event.handshake Journal.handshake?
      Journal.session (Driver.keepaliveObserved Journal.hooks) msg src) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold HandshakeWorker.observedReceive
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after _ _ _ _ _)
    | ciphertext_handshake_source

theorem handshake : StateSafe (Driver.handshakeObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold Driver.handshakeObserved
  dsimp only [Journal.hooks]
  unfold HandshakeWorker.observed HandshakeWorker.workerWith
  repeat' first
    | (nonce_source_head HandshakeWorker.observedReceive; exact handshake_receive _ _)
    | ciphertext_handshake_source

theorem receive_iteration : ProductSafe (Driver.receiveIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (product_state handshake)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
