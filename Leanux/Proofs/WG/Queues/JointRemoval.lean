import Leanux.Proofs.WG.Queues.RemovalAppends

/-! The existing make-dead and removal skeletons share only their actual
completion/access callbacks. Their source equations retain null handling,
nested completion order, normal results and every failed prefix. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes AllowedIps
universe u

def peerMakeDeadWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (remove mark : m Unit) (pid : PeerId) : m Unit := do
  lift (modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)})
  remove
  let d ← lift getDev
  _ ← lift (branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
  lift (modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)})
  mark

def peerRemoveWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (makeDead afterDead : PeerId → m Unit)
    (peer : Option PeerId) : m Unit := do
  if ← lift (branch .peerRemoveNull peer.isNone) then return
  let some pid := peer | lift (invariant "unreachable")
  makeDead pid
  afterDead pid

theorem peerMakeDead_factor (pid : PeerId) :
    WG.peerMakeDead pid = peerMakeDeadWith (fun {_} a => a) (removeByPeer pid)
      (do let p ← getPeer pid; setPeer pid {p with isDead := true}) pid := rfl

theorem peerMakeDeadObserved_factor (pid : PeerId) :
    peerMakeDeadObserved pid = peerMakeDeadWith (fun {_} a => liftWGPrefix a) (completedRemovePeer pid)
      (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with isDead := true})) pid := rfl

theorem peerMakeDeadPrefix_factor (pid : PeerId) :
    peerMakeDeadPrefix pid = peerMakeDeadWith (fun {_} a => liftWGPrefix a) (removeByPeerPrefix pid)
      (modifyPeerKeysPrefix pid (fun p => {p with isDead := true})) pid := rfl

theorem peerRemove_factor (peer : Option PeerId) :
    WG.peerRemove peer = peerRemoveWith (fun {_} a => a) WG.peerMakeDead WG.peerRemoveAfterDead peer := rfl

theorem peerRemoveObserved_factor (peer : Option PeerId) :
    peerRemoveObserved peer = peerRemoveWith (fun {_} a => liftWGPrefix a)
      peerMakeDeadObserved (fun pid => liftWGPrefix (peerRemoveAfterDead pid)) peer := rfl

theorem peerRemovePrefix_factor (peer : Option PeerId) :
    peerRemovePrefix peer = peerRemoveWith (fun {_} a => liftWGPrefix a)
      peerMakeDeadPrefix peerRemoveAfterDeadPrefix peer := rfl

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private theorem makeDead_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α)
    (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (remove mark : WGPrefix E Unit) (remove' mark' : WGPrefix F Unit)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (hr : StateProjectsPrefix ρ id remove remove') (hm : StateProjectsPrefix ρ id mark mark')
    (pid : PeerId) :
    StateProjectsPrefix ρ id (peerMakeDeadWith lift remove mark pid)
      (peerMakeDeadWith lift' remove' mark' pid) := by
  unfold peerMakeDeadWith
  repeat' first
    | with_reducible exact hl _
    | with_reducible exact hr
    | with_reducible exact hm
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | (maintenance_intro; try dsimp only [id_eq])

private theorem remove_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α)
    (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (make after : PeerId → WGPrefix E Unit) (make' after' : PeerId → WGPrefix F Unit)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (hm : ∀ pid, StateProjectsPrefix ρ id (make pid) (make' pid))
    (ha : ∀ pid, StateProjectsPrefix ρ id (after pid) (after' pid)) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (peerRemoveWith lift make after peer) (peerRemoveWith lift' make' after' peer) := by
  unfold peerRemoveWith
  cases peer <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hm _
    | with_reducible exact ha _
    | exact (fun _ _ _ => rfl : StateProjectsPrefix ρ id (pure () : WGPrefix E Unit) (pure () : WGPrefix F Unit))
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])

private abbrev RemovalFocused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (a : WGPrefix E α) : Prop :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.Focused) encode decode g a

private theorem makeDead_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (remove mark : WGPrefix E Unit)
    (hr : StateAppends remove) (hm : StateAppends mark) (pid : PeerId) :
    peerMakeDeadWith (fun {_} a => liftWGPrefix a)
      (focusStatePrefix encode decode remove) (focusStatePrefix encode decode mark) pid =
    focusStatePrefix encode decode (peerMakeDeadWith (fun {_} a => liftWGPrefix a) remove mark pid) := by
  have lifted {α : Type} (a : WG.M α) : RemovalFocused encode decode (liftWGPrefix a) (liftWGPrefix a) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) encode decode a
  have rem : RemovalFocused encode decode (focusStatePrefix encode decode remove) remove := ⟨hr,rfl⟩
  have end' : RemovalFocused encode decode (focusStatePrefix encode decode mark) mark := ⟨hm,rfl⟩
  have whole : RemovalFocused encode decode
      (peerMakeDeadWith (fun {_} a => liftWGPrefix a)
        (focusStatePrefix encode decode remove) (focusStatePrefix encode decode mark) pid)
      (peerMakeDeadWith (fun {_} a => liftWGPrefix a) remove mark pid) := by
    unfold peerMakeDeadWith
    repeat' first
      | with_reducible exact lifted _
      | exact rem
      | exact end'
      | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
      | (maintenance_intro; try dsimp only)
  exact whole.2

private theorem remove_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (make after : PeerId → WGPrefix E Unit)
    (hm : ∀ pid, StateAppends (make pid)) (ha : ∀ pid, StateAppends (after pid)) (peer : Option PeerId) :
    peerRemoveWith (fun {_} a => liftWGPrefix a)
      (fun pid => focusStatePrefix encode decode (make pid))
      (fun pid => focusStatePrefix encode decode (after pid)) peer =
    focusStatePrefix encode decode (peerRemoveWith (fun {_} a => liftWGPrefix a) make after peer) := by
  have lifted {α : Type} (a : WG.M α) : RemovalFocused encode decode (liftWGPrefix a) (liftWGPrefix a) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) encode decode a
  have start (pid : PeerId) : RemovalFocused encode decode (focusStatePrefix encode decode (make pid)) (make pid) := ⟨hm pid,rfl⟩
  have end' (pid : PeerId) : RemovalFocused encode decode (focusStatePrefix encode decode (after pid)) (after pid) := ⟨ha pid,rfl⟩
  have whole : RemovalFocused encode decode
      (peerRemoveWith (fun {_} a => liftWGPrefix a)
        (fun pid => focusStatePrefix encode decode (make pid))
        (fun pid => focusStatePrefix encode decode (after pid)) peer)
      (peerRemoveWith (fun {_} a => liftWGPrefix a) make after peer) := by
    unfold peerRemoveWith
    cases peer <;> dsimp only
    all_goals repeat' first
      | with_reducible exact lifted _
      | with_reducible exact start _
      | with_reducible exact end' _
      | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
      | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
      | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
      | (maintenance_intro; try dsimp only)
  exact whole.2

private theorem makeDead_rx_eq (pid : PeerId) :
    peerMakeDeadWith (fun {_} a => liftWGPrefix a) (nativeRx (removeByPeerPrefix pid))
      (nativeRx (modifyPeerKeysPrefix pid (fun p => {p with isDead := true}))) pid =
      nativeRx (peerMakeDeadPrefix pid) := by
  let remove := removeByPeerPrefix pid
  let mark := modifyPeerKeysPrefix pid (fun p => {p with isDead := true})
  have hr : StateAppends remove :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.replace_appends) pid
  have hm : StateAppends mark := (StateAppends.focus _ _ _).bind (fun _ => StateAppends.focus _ _ _)
  have inner := makeDead_focus AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl) remove mark hr hm pid
  have outer := makeDead_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? remove)
    (focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? mark)
    (StateAppends.focus _ _ _) (StateAppends.focus _ _ _) pid
  rw [peerMakeDeadPrefix_factor]
  exact outer.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner)

private theorem remove_rx_eq (peer : Option PeerId) :
    peerRemoveWith (fun {_} a => liftWGPrefix a)
      (fun pid => nativeRx (peerMakeDeadPrefix pid))
      (fun pid => nativeRx (peerRemoveAfterDeadPrefix pid)) peer = nativeRx (peerRemovePrefix peer) := by
  have hm (pid : PeerId) : StateAppends (peerMakeDeadPrefix pid) :=
    peerMakeDeadPrefix_appends pid
  have inner := remove_focus AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    peerMakeDeadPrefix peerRemoveAfterDeadPrefix hm peerRemoveAfterDeadPrefix_appends peer
  have outer := remove_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun pid => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerMakeDeadPrefix pid))
    (fun pid => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerRemoveAfterDeadPrefix pid))
    (fun _ => StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _) peer
  rw [peerRemovePrefix_factor]
  exact outer.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner)

def makeDead (pid : PeerId) : WGPrefix Event Unit :=
  peerMakeDeadWith (fun {_} a => liftWGPrefix a) (completedRemovePeer pid)
    (access (modifyPeerKeysPrefix pid (fun p => {p with isDead := true}))) pid

def removePeer (peer : Option PeerId) : WGPrefix Event Unit :=
  peerRemoveWith (fun {_} a => liftWGPrefix a) makeDead (fun pid => access (peerRemoveAfterDeadPrefix pid)) peer

theorem makeDead_routing (pid : PeerId) :
    StateProjectsPrefix routingEvent id (makeDead pid) (peerMakeDeadObserved pid) := by
  rw [peerMakeDeadObserved_factor]
  apply makeDead_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact completedRemovePeer_routing pid
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases (modifyPeerKeysPrefix_erases pid _)) (access_routing _)

theorem makeDead_rx (pid : PeerId) :
    StateProjectsPrefix rxEvent id (makeDead pid) (nativeRx (peerMakeDeadPrefix pid)) := by
  rw [← makeDead_rx_eq pid]
  apply makeDead_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact completed_rx _ _
  · exact access_rx _

theorem removePeer_routing (peer : Option PeerId) :
    StateProjectsPrefix routingEvent id (removePeer peer) (peerRemoveObserved peer) := by
  rw [peerRemoveObserved_factor]
  apply remove_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · exact makeDead_routing
  · intro pid
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases (peerRemoveAfterDeadPrefix_erases pid)) (access_routing _)

theorem removePeer_rx (peer : Option PeerId) :
    StateProjectsPrefix rxEvent id (removePeer peer) (nativeRx (peerRemovePrefix peer)) := by
  rw [← remove_rx_eq peer]
  apply remove_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact makeDead_rx
  · intro pid; exact access_rx _

theorem removePeer_rx_product (peer : Option PeerId) :
    ProjectsPrefix rxEvent id (liftWGObserver (removePeer peer))
      (RxHistory.mixed (liftWGObserver (peerRemovePrefix peer))) := by
  rw [← nativeRx_product]
  exact (removePeer_rx peer).liftWGObserver _ _

/-- The update now uses the actual whole removal observer, including both
flushes. No callback projection or append premise remains. -/
theorem peerConfigUpdate_concrete_routing (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix routingEvent id (peerConfigUpdate removePeer attrs peer flags psk pid)
      (peerConfigUpdateObserved attrs peer flags psk pid) :=
  peerConfigUpdate_routing removePeer removePeer_routing attrs peer flags psk pid

theorem peerConfigUpdate_concrete_rx (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix rxEvent id (peerConfigUpdate removePeer attrs peer flags psk pid)
      (nativeRx (peerConfigUpdatePrefix attrs peer flags psk pid)) :=
  peerConfigUpdate_rx_existing removePeer removePeer_rx attrs peer flags psk pid (peerRemovePrefix_appends peer)

theorem peerConfigUpdate_concrete_product (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ProjectsPrefix rxEvent id (liftWGObserver (peerConfigUpdate removePeer attrs peer flags psk pid))
      (RxHistory.mixed (liftWGObserver (peerConfigUpdatePrefix attrs peer flags psk pid))) :=
  peerConfigUpdate_rx_product removePeer removePeer_rx attrs peer flags psk pid (peerRemovePrefix_appends peer)

end Leanux.Proofs.WG.Queues.RoutingJoint
