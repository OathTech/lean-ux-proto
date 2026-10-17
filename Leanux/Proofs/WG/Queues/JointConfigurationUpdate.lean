import Leanux.Proofs.WG.Queues.JointConfigurationTail
import Leanux.Proofs.WG.Configuration.PeerUpdateCompletion

/-! One source factor for acquired-peer updates. Callback domains stay in the
caller's monad; the equations below identify the existing raw, routing and
lifetime observers exactly. Removal remains a supplied operation until its
separate source closure is available. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps
universe u

def peerConfigUpdateWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (remove setPsk replace : m Unit) (endpoint : Endpoint → m Unit)
    (out : Int → m Int) (tail : m Int)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) : m Int := do
  if ← lift (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    remove
    return ← out 0
  if ← lift (branch .peerSetPsk psk.isSome) then setPsk
  if ← lift (branch .peerHasEndpoint attrs.endpoint.isSome) then
    let some e := attrs.endpoint | lift (invariant "unreachable")
    if ← lift (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      endpoint {family := e.family, addr := e.addr, port := e.port}
    else if ← lift (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      endpoint {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo}
  if ← lift (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then replace
  tail

theorem peerConfigUpdateSource_factor (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    peerConfigUpdateSource attrs peer flags psk pid =
      peerConfigUpdateWith (fun {_} a => a) (peerRemove peer)
        (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})
        (removeByPeer pid) (setPeerEndpoint pid)
        (fun ret => do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
        (peerConfigTailSource attrs peer pid) attrs flags psk := by
  simp only [peerConfigUpdateSource,peerConfigUpdateWith,bind_assoc]
  rfl

theorem peerConfigUpdateObserved_factor (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    peerConfigUpdateObserved attrs peer flags psk pid =
      peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (peerRemoveObserved peer)
        (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []}))
        (completedRemovePeer pid) (fun e => liftWGPrefix (setPeerEndpoint pid e))
        (peerConfigOutObserved attrs peer) (peerConfigTailObserved attrs peer pid) attrs flags psk := rfl

theorem peerConfigUpdatePrefix_factor (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    peerConfigUpdatePrefix attrs peer flags psk pid =
      peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (peerRemovePrefix peer)
        (modifyPeerKeysPrefix pid (fun p => {p with presharedKey := psk.getD []}))
        (removeByPeerPrefix pid) (setPeerEndpointPrefix pid)
        (peerConfigOutPrefix attrs peer) (peerConfigTailPrefix attrs peer pid) attrs flags psk := rfl

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private theorem projects_ite {E F α : Type} (ρ : E → Option F)
    (p : Prop) [Decidable p] {a b : WGPrefix E α} {a' b' : WGPrefix F α}
    (ha : p → StateProjectsPrefix ρ id a a') (hb : ¬p → StateProjectsPrefix ρ id b b') :
    StateProjectsPrefix ρ id (if p then a else b) (if p then a' else b') := by
  by_cases h : p
  · simpa only [h,ite_true] using ha h
  · simpa only [h,ite_false] using hb h

theorem peerConfigUpdateWith_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α)
    (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (remove setPsk replace : WGPrefix E Unit) (endpoint : Endpoint → WGPrefix E Unit)
    (out : Int → WGPrefix E Int) (tail : WGPrefix E Int)
    (remove' setPsk' replace' : WGPrefix F Unit) (endpoint' : Endpoint → WGPrefix F Unit)
    (out' : Int → WGPrefix F Int) (tail' : WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (hr : StateProjectsPrefix ρ id remove remove')
    (hs : StateProjectsPrefix ρ id setPsk setPsk')
    (hp : StateProjectsPrefix ρ id replace replace')
    (he : ∀ e, StateProjectsPrefix ρ id (endpoint e) (endpoint' e))
    (ho : ∀ ret, StateProjectsPrefix ρ id (out ret) (out' ret))
    (ht : StateProjectsPrefix ρ id tail tail')
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) :
    StateProjectsPrefix ρ id (peerConfigUpdateWith lift remove setPsk replace endpoint out tail attrs flags psk)
      (peerConfigUpdateWith lift' remove' setPsk' replace' endpoint' out' tail' attrs flags psk) := by
  unfold peerConfigUpdateWith
  cases attrs.endpoint <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hr
    | with_reducible exact hs
    | with_reducible exact hp
    | with_reducible exact he _
    | with_reducible exact ho _
    | with_reducible exact ht
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply projects_ite ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

def peerConfigUpdate (remove : Option PeerId → WGPrefix Event Unit)
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    WGPrefix Event Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (remove peer)
    (access (modifyPeerKeysPrefix pid (fun p => {p with presharedKey := psk.getD []})))
    (completedRemovePeer pid) (fun e => access (setPeerEndpointPrefix pid e))
    (peerConfigOut attrs peer) (peerConfigTail attrs peer pid) attrs flags psk

theorem peerConfigUpdate_routing (remove : Option PeerId → WGPrefix Event Unit)
    (hr : ∀ peer, StateProjectsPrefix routingEvent id (remove peer) (peerRemoveObserved peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix routingEvent id (peerConfigUpdate remove attrs peer flags psk pid)
      (peerConfigUpdateObserved attrs peer flags psk pid) := by
  rw [peerConfigUpdateObserved_factor]
  apply peerConfigUpdateWith_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact hr peer
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases (modifyPeerKeysPrefix_erases _ _)) (access_routing _)
  · exact completedRemovePeer_routing pid
  · intro e
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases (setPeerEndpointPrefix_erases pid e)) (access_routing _)
  · exact peerConfigOut_routing attrs peer
  · exact peerConfigTail_routing attrs peer pid

private abbrev UpdateFocused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (a : WGPrefix E α) : Prop :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.Focused) encode decode g a

private theorem focused_ite {E F α : Type} (encode : E → F) (decode : F → Option E)
    (p : Prop) [Decidable p] {a b : WGPrefix F α} {a' b' : WGPrefix E α}
    (ha : p → UpdateFocused encode decode a a') (hb : ¬p → UpdateFocused encode decode b b') :
    UpdateFocused encode decode (if p then a else b) (if p then a' else b') := by
  by_cases h : p
  · simpa only [h,ite_true] using ha h
  · simpa only [h,ite_false] using hb h

/-- The exact focus law uses the real append facts for the supplied callbacks;
it does not assume their journal outputs are independent of the input history. -/
theorem peerConfigUpdateWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    (remove setPsk replace : WGPrefix E Unit) (endpoint : Endpoint → WGPrefix E Unit)
    (out : Int → WGPrefix E Int) (tail : WGPrefix E Int)
    (hr : StateAppends remove) (hs : StateAppends setPsk) (hp : StateAppends replace)
    (he : ∀ e, StateAppends (endpoint e)) (ho : ∀ ret, StateAppends (out ret)) (ht : StateAppends tail)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) :
    peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
      (focusStatePrefix encode decode remove) (focusStatePrefix encode decode setPsk)
      (focusStatePrefix encode decode replace) (fun e => focusStatePrefix encode decode (endpoint e))
      (fun ret => focusStatePrefix encode decode (out ret)) (focusStatePrefix encode decode tail) attrs flags psk =
    focusStatePrefix encode decode
      (peerConfigUpdateWith (fun {_} a => liftWGPrefix a) remove setPsk replace endpoint out tail attrs flags psk) := by
  have lifted {α : Type} (a : WG.M α) : UpdateFocused encode decode
      (liftWGPrefix a) (liftWGPrefix a) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) encode decode a
  have rem : UpdateFocused encode decode (focusStatePrefix encode decode remove) remove := ⟨hr,rfl⟩
  have key : UpdateFocused encode decode (focusStatePrefix encode decode setPsk) setPsk := ⟨hs,rfl⟩
  have rep : UpdateFocused encode decode (focusStatePrefix encode decode replace) replace := ⟨hp,rfl⟩
  have ep (e : Endpoint) : UpdateFocused encode decode (focusStatePrefix encode decode (endpoint e)) (endpoint e) := ⟨he e,rfl⟩
  have cleanup (ret : Int) : UpdateFocused encode decode (focusStatePrefix encode decode (out ret)) (out ret) := ⟨ho ret,rfl⟩
  have finish : UpdateFocused encode decode (focusStatePrefix encode decode tail) tail := ⟨ht,rfl⟩
  have whole : UpdateFocused encode decode
      (peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
        (focusStatePrefix encode decode remove) (focusStatePrefix encode decode setPsk)
        (focusStatePrefix encode decode replace) (fun e => focusStatePrefix encode decode (endpoint e))
        (fun ret => focusStatePrefix encode decode (out ret)) (focusStatePrefix encode decode tail) attrs flags psk)
      (peerConfigUpdateWith (fun {_} a => liftWGPrefix a) remove setPsk replace endpoint out tail attrs flags psk) := by
    unfold peerConfigUpdateWith
    cases attrs.endpoint <;> dsimp only
    all_goals repeat' first
      | with_reducible exact lifted _
      | exact rem
      | exact key
      | exact rep
      | with_reducible exact ep _
      | with_reducible exact cleanup _
      | exact finish
      | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
      | with_reducible apply focused_ite encode decode
      | (maintenance_intro; try dsimp only)
      | split
  exact whole.2

def peerConfigUpdateRx (remove : Option PeerId → WGPrefix RxHistory.Event Unit)
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    WGPrefix RxHistory.Event Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (remove peer)
    (nativeRx (modifyPeerKeysPrefix pid (fun p => {p with presharedKey := psk.getD []})))
    (nativeRx (removeByPeerPrefix pid)) (fun e => nativeRx (setPeerEndpointPrefix pid e))
    (fun ret => nativeRx (peerConfigOutPrefix attrs peer ret))
    (nativeRx (peerConfigTailPrefix attrs peer pid)) attrs flags psk

theorem peerConfigUpdate_rx (remove : Option PeerId → WGPrefix Event Unit)
    (rxRemove : Option PeerId → WGPrefix RxHistory.Event Unit)
    (hr : ∀ peer, StateProjectsPrefix rxEvent id (remove peer) (rxRemove peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix rxEvent id (peerConfigUpdate remove attrs peer flags psk pid)
      (peerConfigUpdateRx rxRemove attrs peer flags psk pid) := by
  apply peerConfigUpdateWith_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact hr peer
  · exact access_rx _
  · exact completed_rx (removeByPeerPrefix pid) (fun _ => .removePeer pid)
  · intro e; exact access_rx _
  · intro ret; exact access_rx _
  · exact peerConfigTail_rx attrs peer pid

private theorem keyUpdate_appends (pid : PeerId) (f : Peer → Peer) :
    StateAppends (modifyPeerKeysPrefix pid f) :=
  (StateAppends.focus _ _ _).bind (fun _ => StateAppends.focus _ _ _)

private theorem endpoint_appends (pid : PeerId) (e : Endpoint) :
    StateAppends (setPeerEndpointPrefix pid e) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  unfold setPeerEndpointPrefix dstCacheResetMixed requireNotPendingMixed
  simp only [pure_bind]
  repeat' first
    | with_reducible exact keyUpdate_appends _ _
    | with_reducible exact read _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.appends_ite)
    | (maintenance_intro; try dsimp only)
    | split

private theorem replace_appends (pid : PeerId) : StateAppends (removeByPeerPrefix pid) := by
  have lifted {α : Type} (a : WG.M α) : StateAppends (liftWGPrefix a : MixedM α) := StateAppends.lift a
  have read (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
  have del (id : NodeId) : StateAppends (listDelPrefix id) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.listDel_appends) id
  unfold removeByPeerPrefix
  repeat' first
    | with_reducible exact del _
    | with_reducible exact read _
    | with_reducible exact lifted _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply stateAppends_forIn
    | with_reducible apply StateAppends.bind
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.appends_ite)
    | (maintenance_intro; try dsimp only)
    | split

/-- Every concrete callback except whole peer removal supplies its unconditional
append fact here. The remaining explicit hypothesis is journal structure, not
an allocation, affiliation, residency, or successful-return assumption. -/
theorem peerConfigUpdateRx_eq (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (removeAppends : StateAppends (peerRemovePrefix peer)) :
    peerConfigUpdateRx (fun p => nativeRx (peerRemovePrefix p)) attrs peer flags psk pid =
      nativeRx (peerConfigUpdatePrefix attrs peer flags psk pid) := by
  have out (ret : Int) : StateAppends (peerConfigOutPrefix attrs peer ret) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.out_appends) attrs peer ret
  let key := modifyPeerKeysPrefix pid (fun p => {p with presharedKey := psk.getD []})
  have inner := peerConfigUpdateWith_focus AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    (peerRemovePrefix peer) key (removeByPeerPrefix pid) (setPeerEndpointPrefix pid)
    (peerConfigOutPrefix attrs peer) (peerConfigTailPrefix attrs peer pid)
    removeAppends (keyUpdate_appends pid _) (replace_appends pid) (endpoint_appends pid) out
    (peerConfigTailPrefix_appends attrs peer pid) attrs flags psk
  have outer := peerConfigUpdateWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemovePrefix peer))
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? key)
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (removeByPeerPrefix pid))
    (fun e => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (setPeerEndpointPrefix pid e))
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigOutPrefix attrs peer ret))
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigTailPrefix attrs peer pid))
    (StateAppends.focus _ _ _) (StateAppends.focus _ _ _) (StateAppends.focus _ _ _)
    (fun _ => StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _) (StateAppends.focus _ _ _)
    attrs flags psk
  rw [peerConfigUpdatePrefix_factor]
  exact outer.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner)

theorem peerConfigUpdate_rx_existing (remove : Option PeerId → WGPrefix Event Unit)
    (hr : ∀ peer, StateProjectsPrefix rxEvent id (remove peer) (nativeRx (peerRemovePrefix peer)))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (removeAppends : StateAppends (peerRemovePrefix peer)) :
    StateProjectsPrefix rxEvent id (peerConfigUpdate remove attrs peer flags psk pid)
      (nativeRx (peerConfigUpdatePrefix attrs peer flags psk pid)) := by
  rw [← peerConfigUpdateRx_eq attrs peer flags psk pid removeAppends]
  exact peerConfigUpdate_rx remove _ hr attrs peer flags psk pid

theorem peerConfigUpdate_rx_product (remove : Option PeerId → WGPrefix Event Unit)
    (hr : ∀ peer, StateProjectsPrefix rxEvent id (remove peer) (nativeRx (peerRemovePrefix peer)))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (removeAppends : StateAppends (peerRemovePrefix peer)) :
    ProjectsPrefix rxEvent id (liftWGObserver (peerConfigUpdate remove attrs peer flags psk pid))
      (RxHistory.mixed (liftWGObserver (peerConfigUpdatePrefix attrs peer flags psk pid))) := by
  rw [← nativeRx_product]
  exact (peerConfigUpdate_rx_existing remove hr attrs peer flags psk pid removeAppends).liftWGObserver _ _

end Leanux.Proofs.WG.Queues.RoutingJoint
