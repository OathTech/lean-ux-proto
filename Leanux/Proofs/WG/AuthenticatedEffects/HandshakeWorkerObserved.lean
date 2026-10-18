import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource

/-! Authentication and callback receipts in the shared native handshake worker.
The session and keepalive bodies remain the caller's observers, retaining their
TX/responder journals at the same source cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def callback (record : HandshakeCausal.Event → E) (kind : HandshakeCausal.Kind)
    (pid : PeerId) (body : WGPrefix E α) : WGPrefix E α := do
  emitStatePrefix (record (.callback kind pid))
  body

def old (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (body : WGPrefix HandshakeCausal.Event α) : WGPrefix E α := focusStatePrefix record decode body

def observedOps (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (mac : HandshakeMac) : Ops (WGPrefix E) where
  step := liftWGPrefix
  session := fun pid => callback record .session pid (session pid)
  modifyPeer := fun pid f => old record decode (HandshakeCausal.call .peerWrite pid (do setPeer pid (f (← getPeer pid))))
  create := fun pid => old record decode (HandshakeCausal.call .responseCreate pid (createResponse pid))
  mac := fun pid msg => old record decode (HandshakeCausal.call .outgoingMac pid (addMacToPacket pid msg))
  send := fun pid msg => old record decode (HandshakeCausal.call .send pid (sendBufferToPeer pid msg))
  derived := fun pid => old record decode (HandshakeCausal.call .sessionDerived pid (timersSessionDerived pid))
  traversal := fun pid => old record decode (HandshakeCausal.call .traversal pid (timersTraversal pid))
  sent := fun pid => old record decode (HandshakeCausal.call .authenticatedSent pid (timersAnyAuthenticatedPacketSent pid))
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => old record decode (HandshakeCausal.initiation {mac with input := msg})
  response := fun msg => old record decode (HandshakeCausal.response {mac with input := msg})
  endpoint := fun pid src => old record decode (HandshakeCausal.call .endpoint pid (setPeerEndpointFromSkb pid src))
  complete := fun pid => old record decode (HandshakeCausal.call .handshakeComplete pid (timersHandshakeComplete pid))
  keepalive := fun pid => callback record .keepalive pid (keepalive pid)
  received := fun pid => old record decode (HandshakeCausal.call .authenticatedReceived pid (timersAnyAuthenticatedPacketReceived pid))
  put := fun peer => liftWGPrefix (WG.peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)


def observedReceive (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (msg : Key) (src : SkbSource) : WGPrefix E Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (observedOps record decode session keepalive ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

def observed (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) : WGPrefix E Bool :=
  workerWith (observedReceive record decode session keepalive)

private theorem focus_other (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) (body : WGPrefix HandshakeCausal.Event α)
    (native : WG.M α) (erases : ErasesStatePrefix body native) :
    StateProjectsPrefix ρ id (old record decode body) (liftWGPrefix native) := by
  intro w a h
  have history := focusPrefix_other record decode ρ quiet (body.run w) a h
  have result := focusStatePrefix_erases record decode erases w a h
  change ((native.run w).run a,h.filterMap ρ) =
    ((runPrefix (focusPrefix record decode (body.run w)) a h).1.map
      (fun ((x,v),b) => ((x,v),b)),
      (runPrefix (focusPrefix record decode (body.run w)) a h).2.filterMap ρ)
  change (runPrefix (focusPrefix record decode (body.run w)) a h).1 = _ at result
  rw [result,history]
  cases (native.run w).run a <;> rfl

private theorem callback_projects (record : HandshakeCausal.Event → E) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix E α) (target : WGPrefix F α) (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (callback record kind pid body) target := by
  intro w a h
  have projected := projects w a (h ++ [record (.callback kind pid)])
  change runStatePrefix target w a (h.filterMap ρ) =
    ((runStatePrefix (callback record kind pid body) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runStatePrefix (callback record kind pid body) w a h).2.filterMap ρ)
  unfold callback
  rw [runStatePrefix_bind,runStatePrefix_emit]
  simpa only [Prod.map,id,Prod.eta,runStatePrefix,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,quiet,Option.toList_none,List.nil_append,List.append_nil] using projected

private theorem capture_projects (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ WGRunWitness.value (captureWGRun action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    ((runWGPrefix (captureWGRun action) w a h).1.map (fun ((x,v),b) => ((x.value,v),b)),
      (runWGPrefix (captureWGRun action) w a h).2.filterMap ρ)
  rw [runWGPrefix_captureWGRun]
  cases run : (action.run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

private theorem after_projects (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateProjectsPrefix ρ id
      (afterMacWith (observedOps record decode sg kg mac) msg src loaded state)
      (afterMacWith (ops sa ka) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [observedOps,ops]
  repeat' first
    | (with_reducible apply callback_projects record ρ quiet; first | exact hs _ | exact hk _)
    | with_reducible exact focus_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
    | with_reducible exact focus_other record decode ρ quiet _ _ (HandshakeCausal.initiation_erases _)
    | with_reducible exact focus_other record decode ρ quiet _ _ (HandshakeCausal.response_erases _)
    | handshake_worker_project_step ρ

theorem observedReceive_projects (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (observedReceive record decode sg kg msg src)
      (receptionWith (ops sa ka) msg src) := by
  unfold observedReceive receptionWith
  simp only [ops]
  apply StateProjectsPrefix.bind ρ id id
  · handshake_worker_project_step ρ
  · intro cookie
    dsimp only [id]
    split
    · apply StateProjectsPrefix.bind ρ id id
      · handshake_worker_project_step ρ
      · intro doneValue; handshake_worker_project_step ρ
    · apply StateProjectsPrefix.bind ρ id id
      · handshake_worker_project_step ρ
      · intro loaded
        apply StateProjectsPrefix.bind ρ WGRunWitness.value id (capture_projects ρ _)
        intro checked
        exact after_projects record decode ρ quiet sg sa kg ka hs hk _ _ _ _ _

theorem observed_projects (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) :
    StateProjectsPrefix ρ id (observed record decode sg kg) (source sa ka) :=
  worker_projects ρ _ _ (observedReceive_projects record decode ρ quiet sg sa kg ka hs hk)

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
