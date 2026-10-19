import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorkers
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialHandshakeFrames

/-! The native handshake observer retains resident TX key material while its
session and keepalive callbacks use the same observed driver. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder AuthenticatedEffects Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem state_emit (e : Journal.Event) (quiet : Journal.encryption? e = none) :
    CarrierSafe (emitStatePrefix e) := by
  have keep (h : List Journal.Event) (w : WGWorld) (_ : Ambient) (hi : Carrier h w) :
      Carrier (h ++ [e]) w :=
    ⟨⟨hi.1.1.mono (fun _ member => List.mem_append_left _ member),hi.1.2.quiet_suffix
      (by simp only [List.filterMap_cons,List.filterMap_nil,quiet])⟩,hi.2⟩
  exact StatePrefixEnsures.emit e (fun h w a hi => (keep h w a hi).1.2) keep

theorem handshake_focus (body : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erase : ErasesStatePrefix body native) (keeps : ∀ h, Preserves (Inv h) native)
    (bounds : Preserves Bounds native) :
    CarrierSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? body) :=
  carrier_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) (body.run w))
    (focusStatePrefix_erases _ _ erase) keeps bounds

theorem handshake_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (keeps : ∀ h, Preserves (Inv h) native) (bounds : Preserves Bounds native) :
    CarrierSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake?
      (HandshakeCausal.call kind pid native)) :=
  handshake_focus _ native (HandshakeCausal.call_erases kind pid native) keeps bounds

theorem handshake_initiation (mac : HandshakeMac) :
    CarrierSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.initiation mac)) :=
  handshake_focus _ _ (HandshakeCausal.initiation_erases mac)
    (fun _ => NativeFrames.initiation mac.input) (bounds_forget (DriverCuts.carrier_initiation mac.input))

theorem handshake_response_read (mac : HandshakeMac) :
    CarrierSafe (HandshakeWorker.old Journal.Event.handshake Journal.handshake? (HandshakeCausal.response mac)) :=
  handshake_focus _ _ (HandshakeCausal.response_erases mac)
    (fun _ => NativeFrames.response mac.input) (bounds_forget (DriverCuts.carrier_response mac.input))

theorem peer_update (pid : PeerId) (f : Peer → Peer) :
    Preserves (Inv h) (do setPeer pid (f (← getPeer pid))) :=
  preserves_bind (NativeFrames.read_peer pid) (fun _ => NativeFrames.set_peer pid _)

theorem capture_carrier (native : WG.M α) (keeps : ∀ h, Preserves (Inv h) native)
    (bounds : Preserves Bounds native) : CarrierSafe (captureWGRun native) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.1.2)
  intro h w a x v b hi run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp (keeps h) w a x v b hi.1.1 run,hi.1.2⟩,
    (hoare_iff_run_ambient _ _ _).mp bounds w a x v b hi.2 run⟩

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Journal.Event α)
    (ha : CarrierSafe a) (hb : CarrierSafe b) : CarrierSafe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem logic (loaded : Bool) (mac : MacState) : CarrierSafe (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply carrier_lift
  · intro h
    unfold WG.orM WG.andM
    simp only [branch]
    repeat' resident_poll_frame
  · apply bounds_forget
    intro labels
    unfold WG.orM WG.andM
    simp only [branch]
    repeat' responder_carrier_poll_step labels

private theorem needs (loaded : Bool) (mac : MacState) : CarrierSafe (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply carrier_lift
  · intro h
    unfold WG.andM
    simp only [branch]
    repeat' resident_poll_frame
  · apply bounds_forget
    intro labels
    unfold WG.andM
    simp only [branch]
    repeat' responder_carrier_poll_step labels

open Lean Meta Elab Tactic in
elab "resident_native_lift" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``StatePrefixPreserves then pure args.back!
    else if target.isAppOf ``StatePrefixEnsures then pure args[args.size - 2]!
    else throwError "not a state-prefix contract"
  unless action.consumeMData.headBeta.isAppOf ``liftWGPrefix do
    throwError "not a native lift"

open Lean Meta Elab Tactic in
elab "resident_old_head " wanted:ident : tactic => withMainContext do
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

macro "resident_bounds_leaf " labels:term : tactic => `(tactic| first
    | (rx_retention_head createResponse; exact DriverCuts.carrier_create_response _ $labels)
    | (rx_retention_head addMacToPacket; exact DriverCuts.carrier_mac _ _ $labels)
    | (rx_retention_head sendBufferToPeer; exact DriverCuts.carrier_send_buffer _ _ $labels)
    | (rx_retention_head timersSessionDerived; exact DriverCuts.carrier_derived _ $labels)
    | (rx_retention_head timersTraversal; exact DriverCuts.carrier_traversal _ $labels)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact DriverCuts.carrier_sent _ $labels)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact DriverCuts.carrier_received _ $labels)
    | (rx_retention_head timersHandshakeComplete; exact DriverCuts.carrier_complete _ _ $labels)
    | (rx_retention_head sendHandshakeCookie; exact DriverCuts.carrier_cookie (Cookies.sendHandshakeCookie_frame _ _) $labels)
    | (rx_retention_head consumeInitiation; exact DriverCuts.carrier_initiation _ $labels)
    | (rx_retention_head consumeResponse; exact DriverCuts.carrier_response _ $labels)
    | (rx_retention_head cookieMessageConsume; exact DriverCuts.carrier_cookie_consume _ $labels)
    | (rx_retention_head setPeerEndpointFromSkb; exact DriverCuts.carrier_endpoint_skb _ _ $labels)
    | (rx_retention_head Cookies.loadPhase; exact DriverCuts.carrier_store Cookies.loadPhase_sameStore $labels)
    | (rx_retention_head cookieValidatePacket
       exact DriverCuts.carrier_cookie (Cookies.cookie_frame_of_view wgStoreView _
         ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView)) $labels)
    | (rx_retention_head WG.orM; unfold WG.orM WG.andM; simp only [branch])
    | (rx_retention_head WG.andM; unfold WG.andM; simp only [branch])
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head hiddenClock64; exact hoare_liftAmbient (AmbientM.hiddenClock64 _) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | responder_carrier_handshake_step $labels)

macro "resident_handshake_source" : tactic => `(tactic| first
  | (nonce_source_head pure; exact carrier_pure _)
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _)
  | (nonce_source_head Journal.session; exact session_carrier _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive_carrier _)
  | (resident_old_head HandshakeCausal.call
     apply handshake_call
     · intro h
       first
         | (rx_retention_head Bind.bind; exact peer_update _ _)
         | (repeat' resident_handshake_frame; done)
     · apply bounds_forget
       intro labels
       repeat' resident_bounds_leaf labels
       done)
  | (resident_old_head HandshakeCausal.initiation; exact handshake_initiation _)
  | (resident_old_head HandshakeCausal.response; exact handshake_response_read _)
  | (nonce_source_head emitStatePrefix; exact state_emit _ rfl)
  | (nonce_source_head WG.orM; exact logic _ _)
  | (nonce_source_head WG.andM; exact needs _ _)
  | (nonce_source_head captureWGRun
     apply capture_carrier
     · intro h; repeat' resident_handshake_frame; done
     · apply bounds_forget
       intro labels
       repeat' resident_bounds_leaf labels
       done)
  | (resident_native_lift
     apply carrier_lift
     · intro h; repeat' resident_handshake_frame; done
     · apply bounds_forget
       intro labels
       repeat' resident_bounds_leaf labels
       done)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (session_origin_intro_forall; try dsimp only))

theorem handshake_response (mac : HandshakeMac) (pid : PeerId) :
    CarrierSafe (responseWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) pid) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' resident_handshake_source

theorem handshake_after (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    CarrierSafe (afterMacWith
      (HandshakeWorker.observedOps Journal.Event.handshake Journal.handshake?
        Journal.session (Driver.keepaliveObserved Journal.hooks) mac) msg src loaded state) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold afterMacWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response _ _)
    | resident_handshake_source
  all_goals exact carrier_pure _

theorem handshake_receive (msg : Key) (src : SkbSource) :
    CarrierSafe (HandshakeWorker.observedReceive Journal.Event.handshake Journal.handshake?
      Journal.session (Driver.keepaliveObserved Journal.hooks) msg src) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold HandshakeWorker.observedReceive
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after _ _ _ _ _)
    | resident_handshake_source

theorem handshake_carrier : CarrierSafe (Driver.handshakeObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
  unfold Driver.handshakeObserved
  dsimp only [Journal.hooks]
  unfold HandshakeWorker.observed HandshakeWorker.workerWith
  repeat' first
    | (nonce_source_head HandshakeWorker.observedReceive; exact handshake_receive _ _)
    | resident_handshake_source

theorem receive_iteration_carrier : ProductSafe (Driver.receiveIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1.2) (product_state handshake_carrier)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
