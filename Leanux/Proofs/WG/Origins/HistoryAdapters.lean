import Lean
import Leanux.Proofs.WG.Origins.SessionMaterial
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.Queues.RxPollComposition
import Leanux.Proofs.Framing.WGDump

/-! Inject the actual session and stored-decrypt receipts into the existing
persistent RX journal. Focus executes each lower observer once and preserves
all incoming audit probes. These local contracts do not establish initialized
material support or observe copied consistency trials. -/
namespace Leanux.Proofs.WG.Origins.HistoryAdapters
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

abbrev HEvent := RxHistory.Event
abbrev Obs := RxHistory.Obs

def encode : Origins.Event → HEvent
  | .life e => .audit (.lifetime e)
  | .session r => .session r
  | .rx r => .rx r

def decode : HEvent → Option Origins.Event
  | .audit (.lifetime e) => some (.life e)
  | .session r => some (.session r)
  | .rx r => some (.rx r)
  | _ => none

def focus (a : PrefixM Origins.Event α) : Obs α := focusPrefix encode decode a

theorem decode_encode (e : Origins.Event) : decode (encode e) = some e := by cases e <;> rfl

theorem input_lifetime (h : List HEvent) :
    (h.filterMap decode).filterMap Origins.lifetime = RxHistory.prior h := by
  simp only [RxHistory.prior, RxHistory.auditHistory, lifetimeHistory, List.filterMap_filterMap]
  congr 1
  funext e
  cases e <;> try rfl
  case audit a => cases a <;> rfl

theorem encoded_audit (s : List Origins.Event) :
    (s.map encode).filterMap RxHistory.auditEvent =
      (s.filterMap Origins.lifetime).map AuditEvent.lifetime := by
  induction s with
  | nil => rfl
  | cons e s ih => cases e <;> simp only [List.map_cons,List.filterMap_cons,encode,RxHistory.auditEvent,Origins.lifetime,ih]

private theorem native_projects {I : List F → WGWorld → Ambient → Prop}
    {g : WGPrefix E α} {a : WGPrefix F α} {ρ : E → Option F}
    (hp : StateProjectsUnder I ρ g a) :
    ProjectsUnder (fun h (w : World) => I h w.wg w.ambient) ρ
      (liftWGObserver g) (liftWGObserver a) := by
  intro w h hi
  have he := hp w.wg w.ambient h hi
  change runWGPrefix a w.wg w.ambient (h.filterMap ρ) =
    ((runWGPrefix g w.wg w.ambient h).1,
      (runWGPrefix g w.wg w.ambient h).2.filterMap ρ) at he
  rw [liftWGObserver_run, liftWGObserver_run, he]

theorem focus_projects (g : PrefixM Origins.Event α) (a : PrefixM LifetimeEvent α)
    (ha : Appends g) (hp : ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime g a) :
    ProjectsUnder AuditInv RxHistory.auditEvent (focus g) (auditFocus a) := by
  intro w h hi
  have projected := hp w (h.filterMap decode) (by simpa only [input_lifetime,RxHistory.prior,RxHistory.auditHistory] using hi.1)
  obtain ⟨s,hs⟩ := ha w (h.filterMap decode)
  have equation : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1,h.filterMap decode ++ s) := Prod.ext rfl hs
  change runPrefix (auditFocus a) w (h.filterMap RxHistory.auditEvent) = _
  unfold auditFocus
  change (_, _) = _
  simp only [focus, focusPrefix_suffix encode decode g w h _ s equation]
  change ((runPrefix a w _).1, _ ++ ((runPrefix a w _).2.drop _).map _) = _
  have input := input_lifetime h
  change (h.filterMap decode).filterMap Origins.lifetime =
    (h.filterMap RxHistory.auditEvent).filterMap AuditEvent.lifetime? at input
  rw [← input,projected]
  simp only [hs,List.filterMap_append,input_lifetime,List.drop_left,encoded_audit]

def session (pid : PeerId) : Obs Bool := focus (liftWGObserver (Origins.localSession pid))
def decrypt (id : SkbId) : Obs (RxPacket × Option RxPacket) := focus (liftWGObserver (Origins.localDecrypt id))

theorem session_erases (pid : PeerId) : ErasesPrefix (session pid) (liftWG (beginSession pid)) :=
  focusPrefix_erases _ _ (liftWGObserver_erases (Origins.localSession_erases pid))

theorem decrypt_erases (id : SkbId) : ErasesPrefix (decrypt id) (liftWG (RxOrigin.readDecrypt id)) :=
  focusPrefix_erases _ _ (liftWGObserver_erases (Origins.localDecrypt_erases id))

theorem session_projects (pid : PeerId) :
    ProjectsUnder AuditInv RxHistory.auditEvent (session pid) (auditFocus (liftWGObserver (beginSessionPrefix pid))) :=
  focus_projects _ _ (StateAppends.focus _ _ _).liftWGObserver (native_projects (Origins.localSession_projects pid))

theorem decrypt_projects (id : SkbId) :
    ProjectsUnder AuditInv RxHistory.auditEvent (decrypt id) (auditFocus (liftWGObserver (RxOrigin.readDecryptPrefix id))) :=
  focus_projects _ _ (StateAppends.focus _ _ _).liftWGObserver (native_projects (Origins.localDecrypt_projects id))

def Valid (h : List HEvent) : Prop := Origins.Valid (h.filterMap decode)

theorem focus_valid (g : PrefixM Origins.Event α)
    (hp : PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid g) :
    PrefixPreserves (fun h _ => Valid h) Valid (focus g) := by
  intro w h hi
  obtain ⟨s,hs,hv,hq⟩ := hp w (h.filterMap decode) hi
  have equation : runPrefix g w (h.filterMap decode) =
    ((runPrefix g w (h.filterMap decode)).1,h.filterMap decode ++ s) := Prod.ext rfl hs
  unfold focus
  change ∃ s, (runPrefix (focusPrefix encode decode g) w h).2 = h ++ s ∧ _
  rw [focusPrefix_suffix encode decode g w h _ s equation]
  have out : Valid (h ++ s.map encode) := by
    unfold Valid
    rw [List.filterMap_append,filterMap_encoded encode decode decode_encode,← hs]
    exact hv
  refine ⟨s.map encode,rfl,out,?_⟩
  cases (runPrefix g w (h.filterMap decode)).1 <;> first | trivial | exact out

theorem session_valid (pid : PeerId) : PrefixPreserves (fun h _ => Valid h) Valid (session pid) :=
  focus_valid _ (Origins.localSession_valid pid).liftWGObserver

theorem decrypt_valid (id : SkbId) : PrefixPreserves (fun h _ => Valid h) Valid (decrypt id) :=
  focus_valid _ (Origins.localDecrypt_valid id).liftWGObserver

theorem focus_other (ρ : HEvent → Option F) (hd : ∀ e, ρ (encode e) = none)
    (g : PrefixM Origins.Event α) :
    ∀ w h, (runPrefix (focus g) w h).2.filterMap ρ = h.filterMap ρ :=
  focusPrefix_other encode decode ρ hd g

theorem focus_preserves (g : PrefixM Origins.Event α) (a : PrefixM LifetimeEvent α)
    (hp : ProjectsUnder AuditInv RxHistory.auditEvent (focus g) (auditFocus a))
    (ha : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe a) :
    PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe (focus g) := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := Appends.focus encode decode g w h
  change (runPrefix (focus g) w h).2 = h ++ suffix at hs
  have projected := hp.preserves (auditFocus_preserves ha) w h hi.audit
  have entries := focus_other RxHistory.entryEvent (by intro e; cases e <;> rfl) g w h
  have stamps : RxHistory.stamps (runPrefix (focus g) w h).2 = RxHistory.stamps h :=
    congrArg (List.map RxJoint.Entry.stamp) entries
  refine ⟨suffix,hs,⟨projected.1,stamps ▸ hi.distinct⟩,?_⟩
  cases hr : (runPrefix (focus g) w h).1 with
  | error e => trivial
  | ok out =>
    refine ⟨by simpa only [hr,RxHistory.auditHistory] using projected.2,stamps ▸ hi.distinct,?_⟩
    intro s hm
    have old := hi.released s (stamps ▸ hm)
    rw [hs]
    exact (RxHistory.released_append h suffix s).mpr (Or.inl old)

theorem session_preserves (pid : PeerId) :
    PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe (session pid) :=
  focus_preserves _ _ (session_projects pid)
    (beginSessionPrefix_preserves_ambient allocationAmbient allocationHandshakeReceive.create
      allocationHandshakeReceive.put allocationHandshakeReceive.replace pid).liftWGObserver

theorem decrypt_preserves (id : SkbId) :
    PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe (decrypt id) :=
  focus_preserves _ _ (decrypt_projects id) (RxOrigin.readDecrypt_allocation id).liftWGObserver

def life (a : PrefixM LifetimeEvent α) : PrefixM Origins.Event α :=
  focusPrefix Origins.Event.life Origins.lifetime a

theorem life_erases (he : ErasesPrefix a original) : ErasesPrefix (life a) original :=
  focusPrefix_erases _ _ he

theorem life_projects (ha : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe a) :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime (life a) a :=
  ha.projects_focus _ _ (fun _ => rfl)

theorem life_valid (a : PrefixM LifetimeEvent α) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (life a) := by
  intro w h hi
  obtain ⟨s,hs⟩ := Appends.focus Origins.Event.life Origins.lifetime a w h
  have hv : Origins.Valid (runPrefix (life a) w h).2 := by
    intro e he
    change e ∈ h ++ _ at he
    rcases List.mem_append.mp he with he | he
    · exact hi e he
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
      trivial
  refine ⟨s,hs,hv,?_⟩
  cases (runPrefix (life a) w h).1 <;> first | trivial | exact hv

def ops : HandshakeSources.Ops (PrefixM Origins.Event) where
  step := fun a => liftPrefix (liftWG a)
  session := fun pid => liftWGObserver (Origins.localSession pid)
  modifyPeer := fun pid f => life (liftWGObserver (modifyPeerKeysPrefix pid f))
  create := fun pid => life (liftWGObserver (createResponsePrefix pid))
  mac := fun pid msg => life (liftWGObserver (addMacToPacketPrefix pid msg))
  send := fun pid msg => life (liftWGObserver (sendBufferToPeerPrefix pid msg))
  derived := fun pid => life (liftWGObserver (timersSessionDerivedPrefix pid))
  traversal := fun pid => life (liftWGObserver (timersTraversalPrefix pid))
  sent := fun pid => life (liftWGObserver (timersAnyAuthenticatedPacketSentPrefix pid))
  cookie := fun msg src => life (liftWGObserver (sendHandshakeCookiePrefix msg src))
  initiation := fun msg => life (liftWGObserver (consumeInitiationPrefix msg))
  response := fun msg => life (liftWGObserver (consumeResponsePrefix msg))
  endpoint := fun pid src => life (liftWGObserver (setPeerEndpointFromSkbPrefix pid src))
  complete := fun pid => life (liftWGObserver (timersHandshakeCompletePrefix pid))
  keepalive := fun pid => life (liftWGObserver (sendKeepalivePrefix pid))
  received := fun pid => life (liftWGObserver (timersAnyAuthenticatedPacketReceivedPrefix pid))
  put := fun pid => life (liftWGObserver (peerPutMixed pid))
  cookieConsume := fun msg => life (liftWGObserver (cookieMessageConsumePrefix msg))

def localResponse (pid : PeerId) := HandshakeSources.responseWith ops pid
def localAfterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :=
  HandshakeSources.afterMacWith ops msg src loaded mac
def localReception (msg : List UInt8) (src : SkbSource) := HandshakeSources.receptionWith ops msg src
def localStep := HandshakeSources.stepWith ops

theorem localResponse_eq (pid : PeerId) : localResponse pid = HandshakeSources.responseWith ops pid := rfl
theorem localAfterMac_eq (msg src loaded mac) : localAfterMac msg src loaded mac = HandshakeSources.afterMacWith ops msg src loaded mac := rfl
theorem localReception_eq (msg src) : localReception msg src = HandshakeSources.receptionWith ops msg src := rfl


def localPrepare : PrefixM Origins.Event (Option PeerId) :=
  focusPrefix Origins.rxEncode Origins.rxDecode (liftWGObserver RxOrigin.prepare)

theorem localPrepare_appends : Appends localPrepare := Appends.focus _ _ _
theorem localPrepare_erases : ErasesPrefix localPrepare (liftWG RxWorkers.prepareSource) :=
  focusPrefix_erases _ _ (liftWGObserver_erases RxOrigin.prepare_erases)

theorem localPrepare_projects :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime
      localPrepare (liftWGObserver RxWorkers.preparePrefix) := by
  apply Origins.adapter_projects _ _ (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)
    _ _ _ (native_projects RxOrigin.prepare_projects)
  apply StateAppends.liftWGObserver
  unfold RxOrigin.prepare RxOrigin.prepareWith RxOrigin.decrypt
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible exact (StateAppends.focus _ _ _).receiptWGObserved _
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only; try simp only [liftWG_bind, liftWG_pure, liftWGObserver_bind, liftWGObserver_pure, apply_ite])
    | split
  all_goals repeat' first
    | exact StateAppends.lift _
    | exact StateAppends.focus _ _ _
    | apply StateAppends.receiptWGObserved

theorem localPrepare_valid :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid localPrepare := by
  apply Origins.focus_valid Origins.rxEncode Origins.rxDecode
    (fun e => match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r)
    (liftWGObserver RxOrigin.prepare)
  · intro e x hv hx
    cases e <;> simp only [Origins.rxDecode,Option.some.injEq,reduceCtorEq] at hx
    all_goals subst x; exact hv
  · intro e hv; cases e <;> exact hv
  · intro w h hi
    have input : MaterialOrigin.Valid RxOrigin.Receipt.Valid h := by
      intro e he; cases e <;> exact hi _ he
    obtain ⟨s,hs,hv,hq⟩ := RxOrigin.prepare_valid.liftWGObserver w h input
    have truth : ∀ e ∈ (runPrefix (liftWGObserver RxOrigin.prepare) w h).2,
        (match e with | .life _ => True | .receipt r => RxOrigin.Receipt.Valid r) := by
      intro e he; cases e <;> exact hv _ he
    refine ⟨s,hs,truth,?_⟩
    cases (runPrefix (liftWGObserver RxOrigin.prepare) w h).1 <;> first | trivial | exact truth



macro "origin_erases_steps" : tactic => `(tactic|
  first
    | with_reducible exact liftWGObserver_erases (Origins.localSession_erases _)
    | with_reducible (rw [← liftWG_bind]; exact life_erases (liftWGObserver_erases (modifyPeerKeysPrefix_erases _ _)))
    | with_reducible exact life_erases (liftWGObserver_erases (createResponsePrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (addMacToPacketPrefix_erases _ _))
    | with_reducible exact life_erases (liftWGObserver_erases (sendBufferToPeerPrefix_erases _ _))
    | with_reducible exact life_erases (liftWGObserver_erases (timersSessionDerivedPrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (timersTraversalPrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (timersAnyAuthenticatedPacketSentPrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (sendHandshakeCookiePrefix_erases _ _))
    | with_reducible exact life_erases (liftWGObserver_erases (consumeInitiationPrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (consumeResponsePrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (setPeerEndpointFromSkbPrefix_erases _ _))
    | with_reducible exact life_erases (liftWGObserver_erases (timersHandshakeCompletePrefix_erases _ _))
    | with_reducible exact life_erases (liftWGObserver_erases (sendKeepalivePrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (timersAnyAuthenticatedPacketReceivedPrefix_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (peerPutMixed_erases _))
    | with_reducible exact life_erases (liftWGObserver_erases (cookieMessageConsumePrefix_erases _))
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (session_origin_intro_forall; try dsimp only; try simp only [liftWG_bind, liftWG_pure, liftWGObserver_bind, liftWGObserver_pure, apply_ite])
    | (with_reducible split <;> try simp only [liftWG_bind, liftWG_pure, liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift]))

theorem localResponse_erases (pid : PeerId) : ErasesPrefix (localResponse pid) (liftWG (sendHandshakeResponse pid)) := by
  rw [← HandshakeSources.response_original]
  unfold localResponse HandshakeSources.responseWith
  dsimp only [ops, HandshakeSources.original]
  simp only [liftWG_bind, liftWG_pure, apply_ite]
  repeat' first
    | origin_erases_steps

theorem localAfterMac_erases (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) : ErasesPrefix (localAfterMac msg src loaded mac) (liftWG (Cookies.afterMac msg src loaded mac)) := by
  rw [← HandshakeSources.afterMac_original]
  unfold localAfterMac HandshakeSources.afterMacWith
  simp only [← localResponse_eq, HandshakeSources.response_original]
  dsimp only [ops, HandshakeSources.original]
  simp only [liftWG_bind, liftWG_pure, apply_ite]
  change ErasesPrefix _ _
  repeat' first
    | with_reducible exact localResponse_erases _
    | origin_erases_steps

theorem localReception_erases (msg : List UInt8) (src : SkbSource) : ErasesPrefix (localReception msg src) (liftWG (receiveHandshakePacket msg src)) := by
  rw [← HandshakeSources.reception_original]
  unfold localReception HandshakeSources.receptionWith
  simp only [← localAfterMac_eq, HandshakeSources.afterMac_original]
  dsimp only [ops, HandshakeSources.original]
  simp only [liftWG_bind, liftWG_pure, apply_ite]
  repeat' first
    | with_reducible exact localAfterMac_erases _ _ _ _
    | origin_erases_steps

theorem localStep_erases  : ErasesPrefix (localStep ) (liftWG receiveStep) := by
  rw [← HandshakeSources.step_original]
  unfold localStep HandshakeSources.stepWith
  simp only [← localReception_eq, HandshakeSources.reception_original]
  dsimp only [ops, HandshakeSources.original]
  simp only [liftWG_bind]
  repeat' first
    | with_reducible exact localReception_erases _ _
    | origin_erases_steps

private theorem pop_allocation (ring : PtrRing (List UInt8 × SkbSource)) :
    PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with handshakeQueue := ring}))) := (allocationReceiveQueue.pop ring).liftWGObserver
private theorem decrement_allocation :
    PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}))) := allocationReceiveQueue.decrement.liftWGObserver

/-- Reject non-leaf contracts before attempting the native lift bridge. -/
elab "origin_allocation_goal" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``PrefixPreserves do Lean.throwError "not an allocation preservation goal"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing observed action"
  let action := args.back!.consumeMData
  unless action.isAppOf ``liftPrefix || action.isAppOf ``liftWGObserver ||
      action.isAppOf ``Pure.pure do
    Lean.throwError "not a leaf preservation goal"

macro "origin_allocation" : tactic => `(tactic|
  (origin_allocation_goal
   first
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible exact pop_allocation _
    | with_reducible exact decrement_allocation
    | (try simp only [← liftWGObserver_lift]
       apply PrefixEnsures.preserves
       apply StatePrefixEnsures.liftWGObserver (P := fun h w _ => AllocationInv h w) (Q := fun _ h w _ => AllocationInv h w)
       first
       | (maintenance_lift_action_head hiddenClock64; exact (allocation_state_store _ (by intro initial; exact hoare_liftAmbient (AmbientM.hiddenClock64 _) _)))
       | (maintenance_head modifyPeerKeysPrefix; apply AmbientContracts.drop; apply modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True); intro p; rfl)
       | (maintenance_head createResponsePrefix; exact (createResponsePrefix_preserves allocationAmbient allocationHandshakeReceive.index _))
       | (maintenance_head addMacToPacketPrefix; exact (addMacToPacketPrefix_preserves allocationAmbient _ _))
       | (maintenance_head beginSessionPrefix; exact (beginSessionPrefix_preserves_ambient allocationAmbient allocationHandshakeReceive.create allocationHandshakeReceive.put allocationHandshakeReceive.replace _))
       | (maintenance_head timersSessionDerivedPrefix; exact (AmbientContracts.drop (timersSessionDerivedPrefix_spec allocationAmbient (fun _ => True) _)))
       | (maintenance_head timersTraversalPrefix; exact (AmbientContracts.drop (timersTraversalPrefix_spec allocationAmbient (fun _ => True) _)))
       | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact (AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec allocationAmbient (fun _ => True) _)))
       | (maintenance_head sendBufferToPeerPrefix; exact (AmbientContracts.drop (sendBufferToPeerPrefix_spec allocationAmbient allocationHandshakeReceive.socket (fun _ => True) _ _)))
       | (maintenance_head sendHandshakeCookiePrefix; exact (sendHandshakeCookiePrefix_preserves allocationAmbient allocationHandshakeReceive _ _))
       | (maintenance_head consumeInitiationPrefix; exact (consumeInitiationPrefix_preserves allocationAmbient _))
       | (maintenance_head consumeResponsePrefix; exact (consumeResponsePrefix_preserves allocationAmbient _))
       | (maintenance_head setPeerEndpointFromSkbPrefix; exact (setPeerEndpointFromSkbPrefix_preserves allocationAmbient _ _))
       | (maintenance_head timersHandshakeCompletePrefix; exact (AmbientContracts.drop (timersHandshakeCompletePrefix_spec allocationAmbient (fun _ => True) _ _)))
       | (maintenance_head sendKeepalivePrefix; exact (sendKeepalivePrefix_preserves_ambient allocationAmbient allocationHandshakeReceive.tx _))
       | (maintenance_lift_action_head modifyDev; exact (allocationHandshakeReceive.stats _))
       | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact (AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec allocationAmbient (fun _ => True) _)))
       | (maintenance_head peerPutMixed; exact (allocationAmbient.peerPut _))
       | (maintenance_head cookieMessageConsumePrefix; exact (cookieMessageConsumePrefix_preserves allocationAmbient _))
       | (maintenance_lift_action_head Cookies.loadPhase; exact (allocation_state_store _ Cookies.loadPhase_sameStore))
       | (maintenance_lift_action_head cookieValidatePacket; exact (AmbientContracts.drop (cookieLift_spec allocationAmbient allocationHandshakeReceive.cookie (fun _ => True) _ ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView))))
       | (maintenance_lift_action_head getDev; exact (allocation_state_store _ getDev_sameWGStore))
       | (maintenance_lift_action_head WG.orM
          apply allocation_state_store
          apply orM_sameView
          all_goals apply andM_sameView
          all_goals intro initial
          all_goals exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))
       | (maintenance_lift_action_head WG.andM
          apply allocation_state_store
          apply andM_sameView
          all_goals intro initial
          all_goals exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))
       | (maintenance_lift_action_head branch; exact (allocation_state_store _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
       | (maintenance_lift_action_head invariant; exact (AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _))))))


private theorem project_ite {E F α : Type} {I : List F → World → Prop}
    {ρ : E → Option F} {gt ge : PrefixM E α} {bt be : PrefixM F α}
    (p : Prop) [Decidable p]
    (ht : p → ProjectsUnder I ρ gt bt) (he : ¬ p → ProjectsUnder I ρ ge be) :
    ProjectsUnder I ρ (if p then gt else ge) (if p then bt else be) := by
  by_cases h : p
  · simpa only [h,ite_true] using ht h
  · simpa only [h,ite_false] using he h

macro "origin_project_steps" : tactic => `(tactic|
  first
    | with_reducible exact native_projects (Origins.localSession_projects _)
    | with_reducible apply life_projects
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | origin_allocation
    | with_reducible apply project_ite
    | with_reducible apply projectsUnder_bind (S := LifetimeEvent.Safe)
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (session_origin_intro_forall; try dsimp only; try simp only [liftWG_bind, liftWG_pure, liftWGObserver_bind, liftWGObserver_pure, apply_ite])
    | (with_reducible split <;> try simp only [liftWG_bind, liftWG_pure, liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift]))

theorem localResponse_projects (pid : PeerId) :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime (localResponse pid) (liftWGObserver (sendHandshakeResponsePrefix pid)) := by
  rw [← HandshakeSources.response_prefix]
  unfold localResponse HandshakeSources.responseWith
  dsimp only [ops, HandshakeSources.prefixOps]
  simp only [liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift, apply_ite]
  repeat' first
    | origin_project_steps

-- This source continuation has the same bounded fanout as Lifetimes.HandshakeReceive.
set_option maxHeartbeats 800000 in
theorem localAfterMac_projects (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime (localAfterMac msg src loaded mac) (liftWGObserver (afterMacPrefix msg src loaded mac)) := by
  rw [← HandshakeSources.afterMac_prefix]
  unfold localAfterMac HandshakeSources.afterMacWith
  simp only [← localResponse_eq, HandshakeSources.response_prefix]
  dsimp only [ops, HandshakeSources.prefixOps]
  simp only [liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift, apply_ite]
  repeat' first
    | with_reducible exact localResponse_projects _
    | with_reducible exact (sendHandshakeResponsePrefix_preserves allocationAmbient allocationHandshakeReceive.socket allocationHandshakeReceive.index allocationHandshakeReceive.create allocationHandshakeReceive.put allocationHandshakeReceive.replace _).liftWGObserver.preserves
    | origin_project_steps

theorem localReception_projects (msg : List UInt8) (src : SkbSource) :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime (localReception msg src) (liftWGObserver (receiveHandshakePacketPrefix msg src)) := by
  rw [← HandshakeSources.reception_prefix]
  unfold localReception HandshakeSources.receptionWith
  simp only [← localAfterMac_eq, HandshakeSources.afterMac_prefix]
  dsimp only [ops, HandshakeSources.prefixOps]
  simp only [liftWGObserver_bind, liftWGObserver_pure, liftWGObserver_lift, apply_ite]
  repeat' first
    | with_reducible exact localAfterMac_projects _ _ _ _
    | with_reducible exact (afterMacPrefix_preserves allocationAmbient allocationHandshakeReceive _ _ _ _).liftWGObserver.preserves
    | origin_project_steps

theorem localStep_projects  :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) Origins.lifetime (localStep ) (liftWGObserver receiveStepPrefix) := by
  rw [← HandshakeSources.step_prefix]
  unfold localStep HandshakeSources.stepWith
  simp only [← localReception_eq, HandshakeSources.reception_prefix]
  dsimp only [ops, HandshakeSources.prefixOps]
  simp only [liftWGObserver_bind, liftWGObserver_lift]
  have getAllocation : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg)
      LifetimeEvent.Safe (liftPrefix (liftWG getDev)) := by
    simpa only [liftWGObserver_lift] using
      (allocation_state_store getDev getDev_sameWGStore).liftWGObserver.preserves
  have branchAllocation (b : Bool) : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg)
      LifetimeEvent.Safe (liftPrefix (liftWG (branch .workerConsumed b))) := by
    simpa only [liftWGObserver_lift] using
      (allocation_state_store (branch .workerConsumed b) (fun initial =>
        hoare_liftAmbient (AmbientM.branch .workerConsumed b)
          (fun w => wgStoreView w = initial))).liftWGObserver.preserves
  apply projectsUnder_bind (projectsUnder_lift _ _) getAllocation
  intro d
  cases hc : d.handshakeQueue.consume with
  | mk item ring =>
    cases item with
    | none =>
      simp only [liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure]
      apply projectsUnder_bind (projectsUnder_lift _ _) (branchAllocation false)
      intro _
      exact projectsUnder_pure _ _
    | some pair =>
      rcases pair with ⟨msg, src⟩
      simp only [liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure]
      apply projectsUnder_bind (projectsUnder_lift _ _) (branchAllocation true)
      intro _
      apply projectsUnder_bind (projectsUnder_lift _ _)
        (by simpa only [liftWGObserver_lift] using pop_allocation ring)
      intro _
      apply projectsUnder_bind (localReception_projects msg src)
        (receiveHandshakePacketPrefix_preserves allocationAmbient
          allocationHandshakeReceive msg src).liftWGObserver.preserves
      intro _
      apply projectsUnder_bind (projectsUnder_lift _ _)
        (by simpa only [liftWGObserver_lift] using decrement_allocation)
      intro _
      exact projectsUnder_pure _ _

private theorem valid_pure (x : α) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (pure x : PrefixM Origins.Event α) :=
  PrefixPreserves.pure (I := fun h _ => Origins.Valid h) (S := Origins.Valid) (fun _ _ hi => hi) x

private theorem valid_lift (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

private theorem appends_ite {E α : Type} {gt ge : PrefixM E α}
    (p : Prop) [Decidable p] (ht : p → Appends gt) (he : ¬ p → Appends ge) :
    Appends (if p then gt else ge) := by
  by_cases h : p
  · simpa only [h,ite_true] using ht h
  · simpa only [h,ite_false] using he h

theorem localResponse_valid (pid : PeerId) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (localResponse pid) := by
  unfold localResponse HandshakeSources.responseWith
  dsimp only [ops]
  repeat' first
    | with_reducible exact life_valid _
    | with_reducible exact (Origins.localSession_valid _).liftWGObserver.preserves
    | with_reducible exact valid_lift _
    | with_reducible exact valid_pure _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localAfterMac_valid (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (localAfterMac msg src loaded mac) := by
  unfold localAfterMac HandshakeSources.afterMacWith
  simp only [← localResponse_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localResponse_valid _
    | with_reducible exact life_valid _
    | with_reducible exact (Origins.localSession_valid _).liftWGObserver.preserves
    | with_reducible exact valid_lift _
    | with_reducible exact valid_pure _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localReception_valid (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (localReception msg src) := by
  unfold localReception HandshakeSources.receptionWith
  simp only [← localAfterMac_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localAfterMac_valid _ _ _ _
    | with_reducible exact life_valid _
    | with_reducible exact (Origins.localSession_valid _).liftWGObserver.preserves
    | with_reducible exact valid_lift _
    | with_reducible exact valid_pure _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localStep_valid  :
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid (localStep ) := by
  unfold localStep HandshakeSources.stepWith
  simp only [← localReception_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localReception_valid _ _
    | with_reducible exact life_valid _
    | with_reducible exact (Origins.localSession_valid _).liftWGObserver.preserves
    | with_reducible exact valid_lift _
    | with_reducible exact valid_pure _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localResponse_appends (pid : PeerId) :
    Appends (localResponse pid) := by
  unfold localResponse HandshakeSources.responseWith
  dsimp only [ops]
  repeat' first
    | exact Appends.focus _ _ _
    | exact (StateAppends.focus _ _ _).liftWGObserver
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | with_reducible apply appends_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

set_option maxHeartbeats 800000 in
theorem localAfterMac_appends (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Appends (localAfterMac msg src loaded mac) := by
  unfold localAfterMac HandshakeSources.afterMacWith
  simp only [← localResponse_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localResponse_appends _
    | exact Appends.focus _ _ _
    | exact (StateAppends.focus _ _ _).liftWGObserver
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | with_reducible apply appends_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localReception_appends (msg : List UInt8) (src : SkbSource) :
    Appends (localReception msg src) := by
  unfold localReception HandshakeSources.receptionWith
  simp only [← localAfterMac_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localAfterMac_appends _ _ _ _
    | exact Appends.focus _ _ _
    | exact (StateAppends.focus _ _ _).liftWGObserver
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | with_reducible apply appends_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem localStep_appends  :
    Appends (localStep ) := by
  unfold localStep HandshakeSources.stepWith
  simp only [← localReception_eq]
  dsimp only [ops]
  repeat' first
    | with_reducible exact localReception_appends _ _
    | exact Appends.focus _ _ _
    | exact (StateAppends.focus _ _ _).liftWGObserver
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | with_reducible apply appends_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

def prepare : Obs (Option PeerId) := focus localPrepare
def receiveStep : Obs Bool := focus localStep

theorem prepare_erases : ErasesPrefix prepare (liftWG RxWorkers.prepareSource) :=
  focusPrefix_erases _ _ localPrepare_erases
theorem receiveStep_erases : ErasesPrefix receiveStep (liftWG WG.receiveStep) :=
  focusPrefix_erases _ _ localStep_erases

theorem prepare_projects : ProjectsUnder AuditInv RxHistory.auditEvent prepare (auditFocus (liftWGObserver RxWorkers.preparePrefix)) :=
  focus_projects _ _ localPrepare_appends localPrepare_projects
theorem receiveStep_projects : ProjectsUnder AuditInv RxHistory.auditEvent receiveStep (auditFocus (liftWGObserver receiveStepPrefix)) :=
  focus_projects _ _ localStep_appends localStep_projects

theorem prepare_preserves : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe prepare :=
  focus_preserves _ _ prepare_projects RxWorkers.prepare_preserves.liftWGObserver
theorem receiveStep_preserves : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe receiveStep :=
  focus_preserves _ _ receiveStep_projects (HandshakeReceiveCall.allocation .step).liftWGObserver

theorem prepare_valid : PrefixPreserves (fun h _ => Valid h) Valid prepare := focus_valid _ localPrepare_valid
theorem receiveStep_valid : PrefixPreserves (fun h _ => Valid h) Valid receiveStep := focus_valid _ localStep_valid

def receiveIteration : Obs IterResult :=
  workerIterPrefix .receiveWorker none receiveStep (liftPrefix (Env.condResched .receiveWorker))

theorem receiveIteration_erases : ErasesPrefix receiveIteration
    (workerIter .receiveWorker none (liftWG WG.receiveStep) (Env.condResched .receiveWorker)) :=
  workerIterPrefix_erases _ _ receiveStep_erases (erasesPrefix_lift _)

theorem receiveIteration_preserves : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe receiveIteration :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) receiveStep_preserves
    (viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) (fun _ _ _ he hi => ⟨hi.audit.store (congrArg (fun p : ProductStore43 => p.2.2.2) he), hi.distinct, hi.released⟩) (condResched_sameKernel _))

theorem receiveIteration_projects : ProjectsUnder AuditInv RxHistory.auditEvent receiveIteration
    (auditFocus (receiveIterPrefix (liftPrefix (Env.condResched .receiveWorker)))) := by
  unfold receiveIteration receiveIterPrefix workerIterPrefix
  repeat' first
    | with_reducible exact receiveStep_projects
    | exact (show PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe (liftWGObserver receiveStepPrefix) from (HandshakeReceiveCall.allocation .step).liftWGObserver)
    | with_reducible exact RxHistory.projectsFocus_lift _
    | with_reducible exact RxHistory.projectsFocus_pure _
    | with_reducible exact allocation_store World.wg _ ((condResched_sameKernel _).of_factor (fun v : ProductStore43 => v.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))
    | with_reducible exact (allocation_state_store _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))).liftWGObserver
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply RxHistory.projectsFocus_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem focus_history (P : List HEvent → Prop) (g : PrefixM Origins.Event α)
    (hp : ∀ h (s : List Origins.Event), P h → P (h ++ s.map encode)) :
    PrefixPreserves (fun h _ => P h) P (focus g) := by
  intro w h hi
  let suffix := (runPrefix g w (h.filterMap decode)).2.drop (h.filterMap decode).length
  have hv := hp h suffix hi
  refine ⟨suffix.map encode,rfl,hv,?_⟩
  cases (runPrefix (focus g) w h).1 <;> trivial

theorem history_lift (P : List HEvent → Prop) (a : Leanux.M α) :
    PrefixPreserves (fun h _ => P h) P (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

theorem receiveIteration_history (P : List HEvent → Prop)
    (hp : PrefixPreserves (fun h _ => P h) P receiveStep) :
    PrefixPreserves (fun h _ => P h) P receiveIteration :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi) hp (history_lift P _)

theorem receiveIteration_valid : PrefixPreserves (fun h _ => Valid h) Valid receiveIteration :=
  receiveIteration_history Valid receiveStep_valid

end Leanux.Proofs.WG.Origins.HistoryAdapters
