import Leanux.Proofs.WG.Queues.JointRemoval
import Leanux.Proofs.WG.Configuration.PeerCommandCompletion

/-! Shared source factors for the actual peer command and acquisition paths.
Their callbacks retain native execution, arbitrary journals and ordinary errors. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes AllowedIps
universe u

def peerCommandAcquiredWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (create : Key → Option Key → m (Except Int PeerId)) (acquire : PeerId → m Unit)
    (out : Int → m Int) (update : Option PeerId → UInt32 → Option Key → PeerId → m Int)
    (publicKey : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) : m Int := do
  let mut flags := flags
  let mut peer := peer
  if ← lift (branch .peerNotFound peer.isNone) then
    if ← lift (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← out 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let identity := (← lift getDev).staticIdentity
    if ← lift (WG.andM (branch .peerSelfHasIdentity identity.hasIdentity) (branch .peerSelfKeyMatch (publicKey == identity.staticPublic))) then
      return ← out 0
    match ← create publicKey psk with
    | .error e =>
      _ ← lift (branch .peerCreateErr true)
      return ← out e
    | .ok pid =>
      _ ← lift (branch .peerCreateErr false)
      acquire pid
      peer := some pid
  let some pid := peer | lift (invariant "set_peer without a peer")
  update peer flags psk pid

def setPeerCmdWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (lookup : Key → m (Option PeerId))
    (out : Int → m Int)
    (acquired : Key → Option Key → UInt32 → Option PeerId → m Int) (attrs : PeerAttrs) : m Int := do
  if !(← lift (WG.andM (branch .peerHasPubkey attrs.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← out (-EINVAL)
  let some publicKey := attrs.publicKey | lift (invariant "unreachable")
  let psk ← do
    if ← lift (WG.andM (branch .peerHasPsk attrs.presharedKey.isSome) (branch .peerPskLen true)) then pure attrs.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← lift (branch .peerHasFlags attrs.flags.isSome) then flags := attrs.flags.getD 0
  if ← lift (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← out (-EOPNOTSUPP)
  if ← lift (branch .peerHasProtocol attrs.protocolVersion.isSome) then
    if ← lift (branch .peerBadProtocol (attrs.protocolVersion != some 1)) then return ← out (-EPFNOSUPPORT)
  let peer ← lookup publicKey
  acquired publicKey psk flags peer

theorem setPeerCmdSource_factor (attrs : PeerAttrs) :
    setPeerCmdSource attrs = setPeerCmdWith (fun {_} a => a) pubkeyLookup
      (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (peerCommandAcquiredWith (fun {_} a => a) peerCreate peerGet
        (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
        (peerConfigUpdateSource attrs)) attrs := rfl

theorem setPeerCmdObserved_factor (attrs : PeerAttrs) :
    setPeerCmdObserved attrs = setPeerCmdWith (fun {_} a => liftWGPrefix a)
      (fun key => liftWGPrefix (pubkeyLookup key)) (peerConfigOutObserved attrs none)
      (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
        (fun key psk => liftWGPrefix (peerCreate key psk)) (fun pid => liftWGPrefix (peerGet pid))
        (peerConfigOutObserved attrs none) (peerConfigUpdateObserved attrs)) attrs := rfl

theorem setPeerCmdPrefix_factor (attrs : PeerAttrs) :
    setPeerCmdPrefix attrs = setPeerCmdWith (fun {_} a => liftWGPrefix a)
      pubkeyLookupPrefix (peerConfigOutPrefix attrs none)
      (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a) peerCreateMixed peerGetMixed
        (peerConfigOutPrefix attrs none) (peerConfigUpdatePrefix attrs)) attrs := rfl

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

private theorem acquired_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (create : Key → Option Key → WGPrefix E (Except Int PeerId)) (acquire : PeerId → WGPrefix E Unit)
    (out : Int → WGPrefix E Int) (update : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix E Int)
    (create' : Key → Option Key → WGPrefix F (Except Int PeerId)) (acquire' : PeerId → WGPrefix F Unit)
    (out' : Int → WGPrefix F Int) (update' : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (hc : ∀ k p, StateProjectsPrefix ρ id (create k p) (create' k p))
    (hg : ∀ pid, StateProjectsPrefix ρ id (acquire pid) (acquire' pid))
    (ho : ∀ ret, StateProjectsPrefix ρ id (out ret) (out' ret))
    (hu : ∀ p f k pid, StateProjectsPrefix ρ id (update p f k pid) (update' p f k pid))
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (peerCommandAcquiredWith lift create acquire out update key psk flags peer)
      (peerCommandAcquiredWith lift' create' acquire' out' update' key psk flags peer) := by
  unfold peerCommandAcquiredWith
  cases peer <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hc _ _
    | with_reducible exact hg _
    | with_reducible exact ho _
    | with_reducible exact hu _ _ _ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem command_projects {E F : Type} (ρ : E → Option F)
    (lift : {α : Type} → WG.M α → WGPrefix E α) (lift' : {α : Type} → WG.M α → WGPrefix F α)
    (lookup : Key → WGPrefix E (Option PeerId)) (out : Int → WGPrefix E Int)
    (acquired : Key → Option Key → UInt32 → Option PeerId → WGPrefix E Int)
    (lookup' : Key → WGPrefix F (Option PeerId)) (out' : Int → WGPrefix F Int)
    (acquired' : Key → Option Key → UInt32 → Option PeerId → WGPrefix F Int)
    (hl : ∀ {α : Type} (a : WG.M α), StateProjectsPrefix ρ id (lift a) (lift' a))
    (hk : ∀ k, StateProjectsPrefix ρ id (lookup k) (lookup' k))
    (ho : ∀ ret, StateProjectsPrefix ρ id (out ret) (out' ret))
    (ha : ∀ k p f peer, StateProjectsPrefix ρ id (acquired k p f peer) (acquired' k p f peer))
    (attrs : PeerAttrs) :
    StateProjectsPrefix ρ id (setPeerCmdWith lift lookup out acquired attrs)
      (setPeerCmdWith lift' lookup' out' acquired' attrs) := by
  unfold setPeerCmdWith
  cases attrs.publicKey <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hk _
    | with_reducible exact ho _
    | with_reducible exact ha _ _ _ _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_pure) ρ _
    | with_reducible apply StateProjectsPrefix.bind ρ id id
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.projects_ite) ρ
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private abbrev CommandFocused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (a : WGPrefix E α) : Prop :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.Focused) encode decode g a

private theorem acquired_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (create : Key → Option Key → WGPrefix F (Except Int PeerId)) (acquire : PeerId → WGPrefix F Unit)
    (out : Int → WGPrefix F Int) (update : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix F Int)
    (create' : Key → Option Key → WGPrefix E (Except Int PeerId)) (acquire' : PeerId → WGPrefix E Unit)
    (out' : Int → WGPrefix E Int) (update' : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), CommandFocused encode decode (lift a) (lift' a))
    (hc : ∀ k p, CommandFocused encode decode (create k p) (create' k p))
    (hg : ∀ pid, CommandFocused encode decode (acquire pid) (acquire' pid))
    (ho : ∀ ret, CommandFocused encode decode (out ret) (out' ret))
    (hu : ∀ p f k pid, CommandFocused encode decode (update p f k pid) (update' p f k pid))
    (key : Key) (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    CommandFocused encode decode (peerCommandAcquiredWith lift create acquire out update key psk flags peer)
      (peerCommandAcquiredWith lift' create' acquire' out' update' key psk flags peer) := by
  unfold peerCommandAcquiredWith
  cases peer <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hc _ _
    | with_reducible exact hg _
    | with_reducible exact ho _
    | with_reducible exact hu _ _ _ _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem command_focused {E F : Type} (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    (lift : {α : Type} → WG.M α → WGPrefix F α) (lift' : {α : Type} → WG.M α → WGPrefix E α)
    (lookup : Key → WGPrefix F (Option PeerId)) (out : Int → WGPrefix F Int)
    (acquired : Key → Option Key → UInt32 → Option PeerId → WGPrefix F Int)
    (lookup' : Key → WGPrefix E (Option PeerId)) (out' : Int → WGPrefix E Int)
    (acquired' : Key → Option Key → UInt32 → Option PeerId → WGPrefix E Int)
    (hl : ∀ {α : Type} (a : WG.M α), CommandFocused encode decode (lift a) (lift' a))
    (hk : ∀ k, CommandFocused encode decode (lookup k) (lookup' k))
    (ho : ∀ ret, CommandFocused encode decode (out ret) (out' ret))
    (ha : ∀ k p f peer, CommandFocused encode decode (acquired k p f peer) (acquired' k p f peer))
    (attrs : PeerAttrs) :
    CommandFocused encode decode (setPeerCmdWith lift lookup out acquired attrs)
      (setPeerCmdWith lift' lookup' out' acquired' attrs) := by
  unfold setPeerCmdWith
  cases attrs.publicKey <;> dsimp only
  all_goals repeat' first
    | with_reducible exact hl _
    | with_reducible exact hk _
    | with_reducible exact ho _
    | with_reducible exact ha _ _ _ _
    | with_reducible exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure) encode decode _
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind) encode decode hd
    | with_reducible apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_ite) encode decode
    | (maintenance_intro; try dsimp only [id_eq])
    | split

private theorem command_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    (lookup : Key → WGPrefix E (Option PeerId))
    (create : Key → Option Key → WGPrefix E (Except Int PeerId)) (acquire : PeerId → WGPrefix E Unit)
    (out : Int → WGPrefix E Int) (update : Option PeerId → UInt32 → Option Key → PeerId → WGPrefix E Int)
    (hk : ∀ k, StateAppends (lookup k)) (hc : ∀ k p, StateAppends (create k p))
    (hg : ∀ pid, StateAppends (acquire pid)) (ho : ∀ ret, StateAppends (out ret))
    (hu : ∀ p f k pid, StateAppends (update p f k pid)) (attrs : PeerAttrs) :
    setPeerCmdWith (fun {_} a => liftWGPrefix a)
      (fun k => focusStatePrefix encode decode (lookup k))
      (fun ret => focusStatePrefix encode decode (out ret))
      (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
        (fun k p => focusStatePrefix encode decode (create k p))
        (fun pid => focusStatePrefix encode decode (acquire pid))
        (fun ret => focusStatePrefix encode decode (out ret))
        (fun p f k pid => focusStatePrefix encode decode (update p f k pid))) attrs =
    focusStatePrefix encode decode
      (setPeerCmdWith (fun {_} a => liftWGPrefix a) lookup out
        (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a) create acquire out update) attrs) := by
  have lifted {α : Type} (a : WG.M α) : CommandFocused encode decode
      (liftWGPrefix a) (liftWGPrefix a) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift) encode decode a
  exact (command_focused encode decode hd _ _ _ _ _ _ _ _ lifted
    (fun k => ⟨hk k,rfl⟩) (fun ret => ⟨ho ret,rfl⟩)
    (fun k p f peer => acquired_focused encode decode hd _ _ _ _ _ _ _ _ _ _
      lifted (fun k p => ⟨hc k p,rfl⟩) (fun pid => ⟨hg pid,rfl⟩)
      (fun ret => ⟨ho ret,rfl⟩) (fun p f k pid => ⟨hu p f k pid,rfl⟩) k p f peer) attrs).2

theorem pubkeyLookupPrefix_appends (key : Key) : StateAppends (pubkeyLookupPrefix key) := by
  unfold pubkeyLookupPrefix peerGetMaybeZeroPrefix
  repeat' joint_append_step

theorem peerConfigUpdatePrefix_appends (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateAppends (peerConfigUpdatePrefix attrs peer flags psk pid) := by
  unfold peerConfigUpdatePrefix
  repeat' first
    | (joint_append_head peerRemovePrefix; exact peerRemovePrefix_appends _)
    | (joint_append_head peerConfigTailPrefix; exact peerConfigTailPrefix_appends _ _ _)
    | (joint_append_head peerConfigOutPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.out_appends) _ _ _)
    | (joint_append_head removeByPeerPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.replace_appends) _)
    | (joint_append_head setPeerEndpointPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.endpoint_appends) _ _)
    | joint_append_step

def peerCommandAcquired (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) : WGPrefix Event Int :=
  peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
    (fun k p => access (peerCreateMixed k p)) (fun pid => access (peerGetMixed pid))
    (peerConfigOut attrs none) (peerConfigUpdate removePeer attrs) key psk flags peer

def setPeerCommand (attrs : PeerAttrs) : WGPrefix Event Int :=
  setPeerCmdWith (fun {_} a => liftWGPrefix a) (fun k => access (pubkeyLookupPrefix k))
    (peerConfigOut attrs none) (peerCommandAcquired attrs) attrs

theorem setPeerCommand_routing (attrs : PeerAttrs) :
    StateProjectsPrefix routingEvent id (setPeerCommand attrs) (setPeerCmdObserved attrs) := by
  rw [setPeerCmdObserved_factor]
  apply command_projects routingEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
  · intro k
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases (pubkeyLookupPrefix_erases k)) (access_routing _)
  · exact peerConfigOut_routing attrs none
  · intro k p f peer
    apply acquired_projects routingEvent
    · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) routingEvent a
    · intro k p
      exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
        routingEvent (access_erases (peerCreateMixed_erases k p)) (access_routing _)
    · intro pid
      exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
        routingEvent (access_erases (peerGetMixed_erases pid)) (access_routing _)
    · exact peerConfigOut_routing attrs none
    · exact peerConfigUpdate_concrete_routing attrs

private theorem command_rx_eq (attrs : PeerAttrs) :
    setPeerCmdWith (fun {_} a => liftWGPrefix a) (fun k => nativeRx (pubkeyLookupPrefix k))
      (fun ret => nativeRx (peerConfigOutPrefix attrs none ret))
      (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
        (fun k p => nativeRx (peerCreateMixed k p)) (fun pid => nativeRx (peerGetMixed pid))
        (fun ret => nativeRx (peerConfigOutPrefix attrs none ret))
        (fun p f k pid => nativeRx (peerConfigUpdatePrefix attrs p f k pid))) attrs =
      nativeRx (setPeerCmdPrefix attrs) := by
  have out (ret : Int) : StateAppends (peerConfigOutPrefix attrs none ret) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.out_appends) attrs none ret
  have inner := command_focus AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl)
    pubkeyLookupPrefix peerCreateMixed peerGetMixed (peerConfigOutPrefix attrs none) (peerConfigUpdatePrefix attrs)
    pubkeyLookupPrefix_appends (fun _ _ => StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _)
    out (peerConfigUpdatePrefix_appends attrs) attrs
  have outer := command_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (fun k => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (pubkeyLookupPrefix k))
    (fun k p => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerCreateMixed k p))
    (fun pid => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerGetMixed pid))
    (fun ret => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigOutPrefix attrs none ret))
    (fun p f k pid => focusStatePrefix AuditEvent.lifetime AuditEvent.lifetime? (peerConfigUpdatePrefix attrs p f k pid))
    (fun _ => StateAppends.focus _ _ _) (fun _ _ => StateAppends.focus _ _ _)
    (fun _ => StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _)
    (fun _ _ _ _ => StateAppends.focus _ _ _) attrs
  rw [setPeerCmdPrefix_factor]
  exact outer.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner)

theorem setPeerCommand_rx (attrs : PeerAttrs) :
    StateProjectsPrefix rxEvent id (setPeerCommand attrs) (nativeRx (setPeerCmdPrefix attrs)) := by
  rw [← command_rx_eq attrs]
  apply command_projects rxEvent
  · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
  · exact fun k => access_rx _
  · exact fun ret => access_rx _
  · intro k p f peer
    apply acquired_projects rxEvent
    · exact fun {_} a => (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) rxEvent a
    · exact fun k p => access_rx _
    · exact fun pid => access_rx _
    · exact fun ret => access_rx _
    · exact peerConfigUpdate_concrete_rx attrs

theorem setPeerCommand_rx_product (attrs : PeerAttrs) :
    ProjectsPrefix rxEvent id (liftWGObserver (setPeerCommand attrs))
      (RxHistory.mixed (liftWGObserver (setPeerCmdPrefix attrs))) := by
  rw [← nativeRx_product]
  exact (setPeerCommand_rx attrs).liftWGObserver _ _

theorem setPeerCmdPrefix_appends (attrs : PeerAttrs) : StateAppends (setPeerCmdPrefix attrs) := by
  unfold setPeerCmdPrefix
  repeat' first
    | (joint_append_head pubkeyLookupPrefix; exact pubkeyLookupPrefix_appends _)
    | (joint_append_head peerCreateMixed; exact StateAppends.focus _ _ _)
    | (joint_append_head peerConfigUpdatePrefix; exact peerConfigUpdatePrefix_appends _ _ _ _ _)
    | joint_append_step

theorem setPeerCommand_erases (attrs : PeerAttrs) :
    ErasesStatePrefix (setPeerCommand attrs) (WG.setPeerCmd attrs) := by
  intro w ambient h
  have hp := congrArg Prod.fst (setPeerCommand_routing attrs w ambient h)
  have he := setPeerCmdObserved_erases attrs w ambient (h.filterMap routingEvent)
  have same := hp.symm.trans he
  change ((runWGPrefix (setPeerCommand attrs) w ambient h).1.map
    (fun ((x,v),a) => ((x,v),a))) = _ at same
  change (runWGPrefix (setPeerCommand attrs) w ambient h).1 = _
  cases hr : (runWGPrefix (setPeerCommand attrs) w ambient h).1 <;>
    simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
