import Leanux.Proofs.WG.Roaming.HandshakeOverlayBridge
import Leanux.Proofs.WG.Roaming.HandshakeAttemptAuthSource
import Leanux.Proofs.WG.Roaming.HandshakeProjectionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

theorem focus_projects (encode : F → E) (decode : E → Option F)
    (back : ∀ e, decode (encode e) = some e) (a : PrefixT F State α)
    (appends : Appends a) :
    ProjectsPrefix decode id (focusPrefix encode decode a) a := by
  intro w h
  have same := projectsUnder_focus (I := fun _ _ => True) encode decode back
    (fun w h _ => appends w h) w h trivial
  cases hr : (runPrefix (focusPrefix encode decode a) w h).1 <;>
    simpa only [hr, Except.map, id_eq] using same

theorem old_projects (a : PrefixM Origins.Event α) (appends : Appends a) :
    ProjectsPrefix oldEvent id (old a) a :=
  focus_projects Sum.inl oldEvent (fun _ => rfl) a appends

theorem old_native (a : PrefixM Origins.Event α) (native : WG.M α)
    (erases : ErasesPrefix a (liftWG native)) :
    ProjectsPrefix attemptEvent id (old a) (liftPrefix (liftWG native)) :=
  projectsPrefix_focus_other Sum.inl oldEvent attemptEvent (fun _ => rfl) erases

theorem observer_focus (encode : F → E) (decode : E → Option F)
    (a : WGPrefix F α) :
    liftWGObserver (focusStatePrefix encode decode a) =
      focusPrefix encode decode (liftWGObserver a) := by
  funext w h
  rfl

def event (msg : List UInt8) (src : SkbSource) (pid : PeerId) (ep : Endpoint)
    (g : WGWorld) (a : Ambient) : Event :=
  .inr ⟨msg,src,pid,ep,Campaign2.snapshot g a⟩

def nativeOld (a : MixedM α) : WGPrefix Event α :=
  focusStatePrefix Sum.inl oldEvent
    (focusStatePrefix Origins.Event.life Origins.lifetime a)

def endpoint (msg : List UInt8) (pid : PeerId) (src : SkbSource) : WGPrefix Event Unit :=
  EndpointAttempt.fromSkbWith liftWGPrefix
    (fun p ep => EndpointAttempt.beforeCall (event msg src p ep)
      (nativeOld (setPeerEndpointPrefix p ep))) pid src

def endpointOnly (msg : List UInt8) (pid : PeerId) (src : SkbSource) : WGPrefix Attempt Unit :=
  EndpointAttempt.fromSkbWith liftWGPrefix
    (fun p ep => EndpointAttempt.beforeCall
      (fun g a => ⟨msg,src,p,ep,Campaign2.snapshot g a⟩)
      (liftWGPrefix (setPeerEndpoint p ep))) pid src

theorem nativeOld_old (act : MixedM α) :
    StateProjectsPrefix oldEvent id (nativeOld act)
      (focusStatePrefix Origins.Event.life Origins.lifetime act) := by
  intro g
  have hid : Prod.map (@id α) (@id WGWorld) = id := by funext x; cases x; rfl
  change ProjectsPrefix oldEvent (Prod.map id id)
    (focusPrefix Sum.inl oldEvent ((focusStatePrefix Origins.Event.life Origins.lifetime act).run g))
    ((focusStatePrefix Origins.Event.life Origins.lifetime act).run g)
  rw [hid]
  exact focus_projects Sum.inl oldEvent (fun _ => rfl) _ (StateAppends.focus _ _ act g)

theorem nativeOld_product (act : MixedM α) :
    liftWGObserver (nativeOld act) = old (HistoryAdapters.life (liftWGObserver act)) := by
  rw [nativeOld, observer_focus, observer_focus]
  rfl

theorem nativeOld_attempt (act : MixedM α) (original : WG.M α)
    (erases : ErasesStatePrefix act original) :
    StateProjectsPrefix attemptEvent id (nativeOld act) (liftWGPrefix original) := by
  intro g
  have hid : Prod.map (@id α) (@id WGWorld) = id := by funext x; cases x; rfl
  change ProjectsPrefix attemptEvent (Prod.map id id)
    (focusPrefix Sum.inl oldEvent ((focusStatePrefix Origins.Event.life Origins.lifetime act).run g))
    (liftPrefix (original.run g))
  rw [hid]
  exact projectsPrefix_focus_other Sum.inl oldEvent attemptEvent (fun _ => rfl)
    (focusStatePrefix_erases _ _ erases g)

theorem state_focus_lift_bind {β : Type} (enc : F → E) (dec : E → Option F)
    (action : WG.M α) (next : α → WGPrefix F β) :
    focusStatePrefix enc dec (liftWGPrefix action >>= next) =
      (liftWGPrefix action >>= fun x => focusStatePrefix enc dec (next x)) := by
  funext g ambient h
  change runWGPrefix (focusStatePrefix enc dec (liftWGPrefix action >>= next)) g ambient h =
    runWGPrefix (liftWGPrefix action >>= fun x => focusStatePrefix enc dec (next x)) g ambient h
  change ((runStatePrefix (liftWGPrefix action >>= next) g ambient (h.filterMap dec)).1,
    h ++ ((runStatePrefix (liftWGPrefix action >>= next) g ambient (h.filterMap dec)).2.drop
      (h.filterMap dec).length).map enc) = _
  rw [runWGPrefix,runStatePrefix_bind,runStatePrefix_bind]
  simp only [liftWGPrefix,runStatePrefix_lift]
  cases hr : (action.run g).run ambient with
  | error stop => simp only [List.drop_length,List.map_nil,List.append_nil]
  | ok result => rcases result with ⟨⟨x,current⟩,after⟩; rfl

theorem state_focus_lift (enc : F → E) (dec : E → Option F) (action : WG.M α) :
    focusStatePrefix enc dec (liftWGPrefix action) = liftWGPrefix action := by
  funext g ambient h
  change (_,h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc) = _
  simp only [List.drop_length,List.map_nil,List.append_nil]
  rfl

theorem state_focus_pure (enc : F → E) (dec : E → Option F) (x : α) :
    focusStatePrefix enc dec (pure x : WGPrefix F α) = pure x := by
  exact state_focus_lift enc dec (pure x)

theorem fromSkb_focus (enc : LifetimeEvent → E) (dec : E → Option LifetimeEvent)
    (pid : PeerId) (src : SkbSource) :
    focusStatePrefix enc dec (setPeerEndpointFromSkbPrefix pid src) =
      EndpointAttempt.fromSkbWith liftWGPrefix
        (fun p ep => focusStatePrefix enc dec (setPeerEndpointPrefix p ep)) pid src := by
  rw [← EndpointAttempt.fromSkb_prefix]
  unfold EndpointAttempt.fromSkbWith
  rw [state_focus_lift_bind]
  apply congrArg (fun f => liftWGPrefix (endpointFromSkb src) >>= f)
  funext endpoint
  rw [state_focus_lift_bind]
  apply congrArg (fun f => liftWGPrefix (branch .epFromSkbOk endpoint.isSome) >>= f)
  funext success
  cases success <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact state_focus_pure enc dec ()
  · cases endpoint
    · exact state_focus_lift enc dec _
    · rfl

theorem state_lift_projects (decode : E → Option F) (action : WG.M α) :
    StateProjectsPrefix decode id (liftWGPrefix action) (liftWGPrefix action) := by
  intro g
  have hid : Prod.map (@id α) (@id WGWorld) = id := by funext x; cases x; rfl
  change ProjectsPrefix decode (Prod.map id id) (liftPrefix (action.run g)) (liftPrefix (action.run g))
  rw [hid]
  exact projectsPrefix_lift decode _

theorem endpoint_old (msg : List UInt8) (pid : PeerId) (src : SkbSource) :
    ProjectsPrefix oldEvent id (liftWGObserver (endpoint msg pid src))
      (HistoryAdapters.ops.endpoint pid src) := by
  change ProjectsPrefix oldEvent id _ (HistoryAdapters.life (liftWGObserver (setPeerEndpointFromSkbPrefix pid src)))
  unfold HistoryAdapters.life
  rw [← observer_focus]
  apply StateProjectsPrefix.liftWGObserver
  rw [fromSkb_focus]
  exact EndpointAttempt.fromSkb_projects oldEvent _ _ _ _ (state_lift_projects oldEvent)
    (fun p ep => EndpointAttempt.beforeCall_projects oldEvent _ (fun _ _ => rfl) _ _ (nativeOld_old _)) pid src

theorem beforeCall_kept (msg : List UInt8) (src : SkbSource) (pid : PeerId) (ep : Endpoint) :
    StateProjectsPrefix attemptEvent id
      (EndpointAttempt.beforeCall (event msg src pid ep) (nativeOld (setPeerEndpointPrefix pid ep)))
      (EndpointAttempt.beforeCall (fun g a => ⟨msg,src,pid,ep,Campaign2.snapshot g a⟩)
        (liftWGPrefix (setPeerEndpoint pid ep))) := by
  intro g ambient h
  have same := nativeOld_attempt _ _ (setPeerEndpointPrefix_erases pid ep) g ambient
    (h ++ [event msg src pid ep g ambient])
  change runWGPrefix (EndpointAttempt.beforeCall
      (fun g a => ⟨msg,src,pid,ep,Campaign2.snapshot g a⟩)
      (liftWGPrefix (setPeerEndpoint pid ep))) g ambient (h.filterMap attemptEvent) =
    ((runWGPrefix (EndpointAttempt.beforeCall (event msg src pid ep)
      (nativeOld (setPeerEndpointPrefix pid ep))) g ambient h).1.map
        (fun (out,a) => (Prod.map id id out,a)),
      (runWGPrefix (EndpointAttempt.beforeCall (event msg src pid ep)
        (nativeOld (setPeerEndpointPrefix pid ep))) g ambient h).2.filterMap attemptEvent)
  simp only [EndpointAttempt.run_beforeCall]
  simpa only [runWGPrefix,runStatePrefix,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,attemptEvent,event] using same

theorem endpoint_attempt (msg : List UInt8) (pid : PeerId) (src : SkbSource) :
    StateProjectsPrefix attemptEvent id (endpoint msg pid src) (endpointOnly msg pid src) :=
  EndpointAttempt.fromSkb_projects attemptEvent _ _ _ _ (state_lift_projects attemptEvent)
    (beforeCall_kept msg src) pid src


def ops (msg : List UInt8) : HandshakeSources.Ops (PrefixM Event) where
  step := fun action => old (HistoryAdapters.ops.step action)
  session := fun pid => old (HistoryAdapters.ops.session pid)
  modifyPeer := fun pid f => old (HistoryAdapters.ops.modifyPeer pid f)
  create := fun pid => old (HistoryAdapters.ops.create pid)
  mac := fun pid bytes => old (HistoryAdapters.ops.mac pid bytes)
  send := fun pid bytes => old (HistoryAdapters.ops.send pid bytes)
  derived := fun pid => old (HistoryAdapters.ops.derived pid)
  traversal := fun pid => old (HistoryAdapters.ops.traversal pid)
  sent := fun pid => old (HistoryAdapters.ops.sent pid)
  cookie := fun bytes src => old (HistoryAdapters.ops.cookie bytes src)
  initiation := fun bytes => old (HistoryAdapters.ops.initiation bytes)
  response := fun bytes => old (HistoryAdapters.ops.response bytes)
  endpoint := fun pid src => liftWGObserver (endpoint msg pid src)
  complete := fun pid => old (HistoryAdapters.ops.complete pid)
  keepalive := fun pid => old (HistoryAdapters.ops.keepalive pid)
  received := fun pid => old (HistoryAdapters.ops.received pid)
  put := fun pid => old (HistoryAdapters.ops.put pid)
  cookieConsume := fun bytes => old (HistoryAdapters.ops.cookieConsume bytes)

theorem ops_old (msg : List UInt8) :
    HandshakeProjection.OpsProjects oldEvent (ops msg) HistoryAdapters.ops where
  step := fun _ => old_projects _ (Appends.lift _)
  session := fun _ => old_projects _ (StateAppends.focus _ _ _).liftWGObserver
  modifyPeer := fun _ _ => old_projects _ (Appends.focus _ _ _)
  create := fun _ => old_projects _ (Appends.focus _ _ _)
  mac := fun _ _ => old_projects _ (Appends.focus _ _ _)
  send := fun _ _ => old_projects _ (Appends.focus _ _ _)
  derived := fun _ => old_projects _ (Appends.focus _ _ _)
  traversal := fun _ => old_projects _ (Appends.focus _ _ _)
  sent := fun _ => old_projects _ (Appends.focus _ _ _)
  cookie := fun _ _ => old_projects _ (Appends.focus _ _ _)
  initiation := fun _ => old_projects _ (Appends.focus _ _ _)
  response := fun _ => old_projects _ (Appends.focus _ _ _)
  endpoint := fun pid src => endpoint_old msg pid src
  complete := fun _ => old_projects _ (Appends.focus _ _ _)
  keepalive := fun _ => old_projects _ (Appends.focus _ _ _)
  received := fun _ => old_projects _ (Appends.focus _ _ _)
  put := fun _ => old_projects _ (Appends.focus _ _ _)
  cookieConsume := fun _ => old_projects _ (Appends.focus _ _ _)

def productLift {E : Type} : HandshakeEndpoint.Lift (PrefixM E) where
  action := fun a => liftWGObserver (liftWGPrefix a)
  bind := by
    intro α β a f
    rw [← liftWGObserver_bind]
    exact congrArg liftWGObserver (HandshakeEndpoint.prefixLift.bind a f)
  pure := fun _ => rfl
  read_ignore := fun _ => rfl
  abort := fun _ _ => rfl

theorem old_native_observed (a : PrefixM Origins.Event α) (native : WG.M α)
    (erases : ErasesPrefix a (liftWG native)) :
    ProjectsPrefix attemptEvent id (old a) (liftWGObserver (liftWGPrefix native)) := by
  simpa only [liftWGObserver_lift] using old_native a native erases

theorem ops_attempt (msg : List UInt8) :
    HandshakeProjection.OpsProjects attemptEvent (ops msg)
      (HandshakeEndpoint.ops productLift (fun pid src => liftWGObserver (endpointOnly msg pid src))) where
  step := fun _ => old_native_observed _ _ (erasesPrefix_lift _)
  session := fun _ => old_native_observed _ _ (liftWGObserver_erases (Origins.localSession_erases _))
  modifyPeer := fun _ _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (modifyPeerKeysPrefix_erases _ _)))
  create := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (createResponsePrefix_erases _)))
  mac := fun _ _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (addMacToPacketPrefix_erases _ _)))
  send := fun _ _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (sendBufferToPeerPrefix_erases _ _)))
  derived := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (timersSessionDerivedPrefix_erases _)))
  traversal := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (timersTraversalPrefix_erases _)))
  sent := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (timersAnyAuthenticatedPacketSentPrefix_erases _)))
  cookie := fun _ _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (sendHandshakeCookiePrefix_erases _ _)))
  initiation := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (consumeInitiationPrefix_erases _)))
  response := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (consumeResponsePrefix_erases _)))
  endpoint := fun pid src => (endpoint_attempt msg pid src).liftWGObserver _ _
  complete := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (timersHandshakeCompletePrefix_erases _ _)))
  keepalive := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (sendKeepalivePrefix_erases _)))
  received := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (timersAnyAuthenticatedPacketReceivedPrefix_erases _)))
  put := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (peerPutMixed_erases _)))
  cookieConsume := fun _ => old_native_observed _ _ (HistoryAdapters.life_erases (liftWGObserver_erases (cookieMessageConsumePrefix_erases _)))

def reception (msg : List UInt8) (src : SkbSource) : PrefixM Event Unit :=
  HandshakeSources.receptionWith (ops msg) msg src
theorem reception_old (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix oldEvent id (reception msg src) (HistoryAdapters.localReception msg src) :=
  HandshakeProjection.reception_projects _ _ _ (ops_old msg) msg src
theorem reception_attempt (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix attemptEvent id (reception msg src)
      (HandshakeSources.receptionWith
        (HandshakeEndpoint.ops productLift (fun pid src => liftWGObserver (endpointOnly msg pid src))) msg src) :=
  HandshakeProjection.reception_projects _ _ _ (ops_attempt msg) msg src


/-- The designated setter event is appended before its original callback, so
even an error from the setter or its cache-reset tail retains this exact head. -/
theorem setter_attempt_complete (msg : List UInt8) (src : SkbSource) (pid : PeerId) (ep : Endpoint)
    (g : WGWorld) (a : Ambient) (h : List Event) :
    ∃ suffix, (runWGPrefix
      (EndpointAttempt.beforeCall (event msg src pid ep) (nativeOld (setPeerEndpointPrefix pid ep)))
      g a h).2 = h ++ [event msg src pid ep g a] ++ suffix :=
  EndpointAttempt.beforeCall_complete _ _ (StateAppends.focus _ _ _) g a h

theorem setter_attempt_retained (msg : List UInt8) (src : SkbSource) (pid : PeerId) (ep : Endpoint)
    (g : WGWorld) (a : Ambient) (h : List Event) :
    (⟨msg,src,pid,ep,Campaign2.snapshot g a⟩ : Attempt) ∈
      (runWGPrefix
        (EndpointAttempt.beforeCall (event msg src pid ep) (nativeOld (setPeerEndpointPrefix pid ep)))
        g a h).2.filterMap attemptEvent := by
  apply List.mem_filterMap.mpr
  exact ⟨event msg src pid ep g a,
    EndpointAttempt.beforeCall_retains _ _ (StateAppends.focus _ _ _) g a h,rfl⟩


end Leanux.Proofs.WG.Roaming.HandshakeOverlay
