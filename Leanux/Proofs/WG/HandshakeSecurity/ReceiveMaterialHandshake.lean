import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialWorkers
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialHandshakeFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialHandshake

/-! Actual handshake callbacks carry the received allocation certificates and
confirmation history in the same journal. Native state frames and source event
frames are proved separately; no initialization premise is hidden in a leaf. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder AuthenticatedEffects Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem state_emit (e : Journal.Event) (quiet : Quiet e) : StateSafe (emitStatePrefix e) := by
  have keep (h : List Journal.Event) (w : WGWorld) (_ : Ambient) (hi : Carrier h w) :
      Carrier (h ++ [e]) w :=
    ⟨by rw [List.filterMap_append]; exact bounded_append hi.1,
      hi.2.quiet (by simpa using quiet)⟩
  exact StatePrefixEnsures.emit e (fun h w a hi => (keep h w a hi).2) keep

theorem handshake_focus (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erase : ErasesStatePrefix body native) (keeps : ∀ h, Preserves (Bounded h) native) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? body) :=
  state_observed
    (history_focus_state _ _ (fun _ => ⟨rfl,by intro p k r impossible; cases impossible⟩) _)
    (focusStatePrefix_erases _ _ erase) keeps

theorem handshake_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (keeps : ∀ h, Preserves (Bounded h) native) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake?
      (HandshakeCausal.call kind pid native)) :=
  handshake_focus _ native (HandshakeCausal.call_erases kind pid native) keeps

theorem handshake_initiation (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.initiation mac)) :=
  handshake_focus _ _ (HandshakeCausal.initiation_erases mac) (fun _ => HandshakeFrames.initiation mac.input)

theorem handshake_response_read (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.response mac)) :=
  handshake_focus _ _ (HandshakeCausal.response_erases mac) (fun _ => HandshakeFrames.response mac.input)

theorem session (pid : PeerId) : StateSafe (Journal.session pid) :=
  state_observed
    (history_focused_receipt _ _ _ _ (fun _ => ⟨rfl,by intro p k r impossible; cases impossible⟩))
    (focusStatePrefix_erases _ _ (DriverCuts.session_erases pid)) (fun _ => bounded_session pid)

theorem peer_update (pid : PeerId) (f : Peer → Peer) :
    Preserves (Bounded h) (do setPeer pid (f (← getPeer pid))) :=
  preserves_bind (bounded_read_peer pid) (fun _ => bounded_set_peer pid _)

theorem capture (native : WG.M α) (keeps : ∀ h, Preserves (Bounded h) native) :
    StateSafe (captureWGRun native) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.2)
  intro h w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (keeps _) w a x v b hi.1 run,hi.2⟩

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Journal.Event α)
    (ha : StateSafe a) (hb : StateSafe b) : StateSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem logic (loaded : Bool) (mac : MacState) : StateSafe (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply state_native
  intro h
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' receive_bounded_native_step

private theorem needs (loaded : Bool) (mac : MacState) : StateSafe (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply state_native
  intro h
  unfold WG.andM
  simp only [branch]
  repeat' receive_bounded_native_step

macro "receive_handshake_source" : tactic => `(tactic| first
  | (nonce_source_head pure; exact state_pure _)
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _)
  | (nonce_source_head Journal.session; exact session _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (resident_old_head HandshakeCausal.call
     apply handshake_call
     intro h
     first
       | (rx_retention_head Bind.bind; exact peer_update _ _)
       | (repeat' receive_handshake_frame; done))
  | (resident_old_head HandshakeCausal.initiation; exact handshake_initiation _)
  | (resident_old_head HandshakeCausal.response; exact handshake_response_read _)
  | (nonce_source_head emitStatePrefix
     exact state_emit _ ⟨rfl,by intro p k r impossible; cases impossible⟩)
  | (nonce_source_head WG.orM; exact logic _ _)
  | (nonce_source_head WG.andM; exact needs _ _)
  | (nonce_source_head captureWGRun
     apply capture
     intro h; repeat' receive_handshake_frame; done)
  | (resident_native_lift
     apply state_native
     intro h; repeat' receive_handshake_frame; done)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (session_origin_intro_forall; try dsimp only))

theorem handshake_response (mac : HandshakeMac) (pid : PeerId) :
    StateSafe (responseWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) pid) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' receive_handshake_source

theorem handshake_after (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) msg src loaded state) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold afterMacWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response _ _)
    | receive_handshake_source
  all_goals exact state_pure _

theorem handshake_receive (msg : Key) (src : SkbSource) :
    StateSafe (HandshakeWorker.observedReceive Journal.Event.handshake Journal.handshake?
      Journal.session (Driver.keepaliveObserved Journal.hooks) msg src) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold HandshakeWorker.observedReceive
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after _ _ _ _ _)
    | receive_handshake_source

theorem handshake : StateSafe (Driver.handshakeObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold Driver.handshakeObserved
  dsimp only [Journal.hooks]
  unfold HandshakeWorker.observed HandshakeWorker.workerWith
  repeat' first
    | (nonce_source_head HandshakeWorker.observedReceive; exact handshake_receive _ _)
    | receive_handshake_source

theorem receive_iteration : ProductSafe (Driver.receiveIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (product_state handshake)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
