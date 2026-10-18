import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved

/-! The shared handshake observer projects to the existing authenticated
receiver journal on the same execution, including before an internal Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

private theorem focus_self (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (body : WGPrefix HandshakeCausal.Event α) (appends : StateAppends body) :
    StateProjectsPrefix decode id (old record decode body) body := by
  intro w a h
  have exactRun := projectsUnder_focus (I := fun _ (_ : Ambient) => True) record decode inverse
    (fun a h _ => appends w a h) a h True.intro
  change runPrefix (body.run w) a (h.filterMap decode) = _
  rw [exactRun]
  change (_,_) = ((runPrefix (focusPrefix record decode (body.run w)) a h).1.map
    (fun ((x,v),b) => ((x,v),b)),_)
  cases result : (runPrefix (focusPrefix record decode (body.run w)) a h).1 with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

private theorem call_appends (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α) :
    StateAppends (HandshakeCausal.call kind pid native) := by
  unfold HandshakeCausal.call
  apply StateAppends.bind (show StateAppends
    (emitStatePrefix (HandshakeCausal.Event.callback kind pid) : WGPrefix HandshakeCausal.Event Unit) from
    fun _ _ _ => ⟨[HandshakeCausal.Event.callback kind pid],rfl⟩)
  intro doneValue
  exact StateAppends.lift native

private theorem initiation_appends (mac : HandshakeMac) : StateAppends (HandshakeCausal.initiation mac) :=
  StateAppends.focus _ _ _
private theorem response_appends (mac : HandshakeMac) : StateAppends (HandshakeCausal.response mac) :=
  StateAppends.focus _ _ _

private theorem capture_self (decode : E → Option F) (action : WG.M α) :
    StateProjectsPrefix decode id (captureWGRun action) (captureWGRun action) := by
  intro w a h
  change runWGPrefix (captureWGRun action) w a (h.filterMap decode) =
    ((runWGPrefix (captureWGRun action : WGPrefix E _) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (captureWGRun action : WGPrefix E _) w a h).2.filterMap decode)
  rw [runWGPrefix_captureWGRun,runWGPrefix_captureWGRun]
  cases result : (action.run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

private theorem callback_self (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix E α) (native : WG.M α)
    (projects : StateProjectsPrefix decode id body (liftWGPrefix native)) :
    StateProjectsPrefix decode id (callback record kind pid body) (HandshakeCausal.call kind pid native) := by
  intro w a h
  have projected := projects w a (h ++ [record (.callback kind pid)])
  change runStatePrefix (HandshakeCausal.call kind pid native) w a (h.filterMap decode) =
    ((runStatePrefix (callback record kind pid body) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runStatePrefix (callback record kind pid body) w a h).2.filterMap decode)
  unfold HandshakeCausal.call callback
  rw [runStatePrefix_bind,runStatePrefix_emit,runStatePrefix_bind,runStatePrefix_emit]
  simpa only [Prod.map,id,Prod.eta,runStatePrefix,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,inverse,Option.toList_some,List.singleton_append] using projected

private theorem after_causal (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (session pid) (liftWGPrefix (beginSession pid)))
    (hk : ∀ pid, StateProjectsPrefix decode id (keepalive pid) (liftWGPrefix (sendKeepalive pid)))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateProjectsPrefix decode id
      (afterMacWith (observedOps record decode session keepalive mac) msg src loaded state)
      (afterMacWith (HandshakeCausal.ops mac) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [observedOps,HandshakeCausal.ops]
  repeat' first
    | (with_reducible apply callback_self record decode inverse; first | exact hs _ | exact hk _)
    | with_reducible exact focus_self record decode inverse _ (call_appends _ _ _)
    | with_reducible exact focus_self record decode inverse _ (initiation_appends _)
    | with_reducible exact focus_self record decode inverse _ (response_appends _)
    | handshake_worker_project_step decode

theorem observedReceive_causal (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (session pid) (liftWGPrefix (beginSession pid)))
    (hk : ∀ pid, StateProjectsPrefix decode id (keepalive pid) (liftWGPrefix (sendKeepalive pid)))
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix decode id (observedReceive record decode session keepalive msg src)
      (HandshakeCausal.receive msg src) := by
  unfold observedReceive HandshakeCausal.receive
  apply StateProjectsPrefix.bind decode id id
  · handshake_worker_project_step decode
  · intro cookie
    dsimp only [id]
    split
    · apply StateProjectsPrefix.bind decode id id
      · handshake_worker_project_step decode
      · intro doneValue; handshake_worker_project_step decode
    · apply StateProjectsPrefix.bind decode id id
      · handshake_worker_project_step decode
      · intro loaded
        dsimp only [id]
        apply StateProjectsPrefix.bind decode id id
        · exact capture_self decode _
        · intro checked
          exact after_causal record decode inverse session keepalive hs hk _ _ _ _ _

theorem observed_causal (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (session pid) (liftWGPrefix (beginSession pid)))
    (hk : ∀ pid, StateProjectsPrefix decode id (keepalive pid) (liftWGPrefix (sendKeepalive pid))) :
    StateProjectsPrefix decode id (observed record decode session keepalive)
      (workerWith HandshakeCausal.receive) :=
  worker_projects decode _ _ (observedReceive_causal record decode inverse session keepalive hs hk)

private theorem focus_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (body : WGPrefix HandshakeCausal.Event α) (appends : StateAppends body) :
    StateProjectsPrefix decode id (old record decode body) (old id some body) := by
  intro w a h
  have source := focus_self record decode inverse body appends w a h
  have same : runStatePrefix (old id some body) w a (h.filterMap decode) =
      runStatePrefix body w a (h.filterMap decode) := by
    obtain ⟨suffix,hs⟩ := appends w a (h.filterMap decode)
    apply Prod.ext
    · simp only [old,focusStatePrefix,focusPrefix,runStatePrefix,runPrefix,StateT.run,
        ExceptT.run,List.filterMap_some]
      rfl
    · change h.filterMap decode ++
        ((runPrefix (body.run w) a ((h.filterMap decode).filterMap some)).2.drop
          ((h.filterMap decode).filterMap some).length).map id = _
      simp only [List.filterMap_some,hs,List.drop_left,List.map_id]
      exact hs.symm
  change runStatePrefix (old id some body) w a (h.filterMap decode) = _
  rw [same]
  exact source

private theorem callback_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix E α)
    (target : WGPrefix HandshakeCausal.Event α) (projects : StateProjectsPrefix decode id body target) :
    StateProjectsPrefix decode id (callback record kind pid body) (callback id kind pid target) := by
  intro w a h
  have projected := projects w a (h ++ [record (.callback kind pid)])
  change runStatePrefix (callback id kind pid target) w a (h.filterMap decode) =
    ((runStatePrefix (callback record kind pid body) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runStatePrefix (callback record kind pid body) w a h).2.filterMap decode)
  unfold callback
  rw [runStatePrefix_bind,runStatePrefix_emit,runStatePrefix_bind,runStatePrefix_emit]
  simpa only [Prod.map,id,Prod.eta,runStatePrefix,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,inverse,Option.toList_some,List.singleton_append] using projected

private theorem after_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (ka pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateProjectsPrefix decode id
      (afterMacWith (observedOps record decode sg kg mac) msg src loaded state)
      (afterMacWith (observedOps id some sa ka mac) msg src loaded state) := by
  unfold afterMacWith responseWith
  simp only [observedOps]
  repeat' first
    | (with_reducible apply callback_matching record decode inverse; first | exact hs _ | exact hk _)
    | with_reducible exact focus_matching record decode inverse _ (call_appends _ _ _)
    | with_reducible exact focus_matching record decode inverse _ (initiation_appends _)
    | with_reducible exact focus_matching record decode inverse _ (response_appends _)
    | handshake_worker_project_step decode

theorem observedReceive_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (ka pid)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix decode id (observedReceive record decode sg kg msg src)
      (observedReceive id some sa ka msg src) := by
  unfold observedReceive
  repeat' first
    | with_reducible exact after_matching record decode inverse sg sa kg ka hs hk _ _ _ _ _
    | with_reducible exact capture_self decode _
    | handshake_worker_project_step decode

theorem observed_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (inverse : ∀ event, decode (record event) = some event)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (ka pid)) :
    StateProjectsPrefix decode id (observed record decode sg kg) (observed id some sa ka) :=
  worker_projects decode _ _ (observedReceive_matching record decode inverse sg sa kg ka hs hk)

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
