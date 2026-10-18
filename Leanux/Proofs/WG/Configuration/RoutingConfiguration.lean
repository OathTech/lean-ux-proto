import Leanux.Proofs.WG.Configuration.ConsumedRouting
import Leanux.Proofs.WG.Queues.JointNetlink

/-! The joint configuration observer appends its real routing and access
records. Old consume positions remain fixed while routing mutations extend the
same journal. Address-shape premises remain the existing caller premises. -/
namespace Leanux.Proofs.WG.RoutingPosition.Controls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Configuration

private theorem appends_forIn {E α β : Type}
    (xs : List α) (first : β) (f : α → β → WGPrefix E (ForInStep β))
    (hf : ∀ x b, StateAppends (f x b)) : StateAppends (forIn xs first f) := by
  induction xs generalizing first with
  | nil => exact StateAppends.pure first
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply (hf x first).bind
    intro step
    cases step with
    | done b => exact StateAppends.pure b
    | yield b => exact ih b

private theorem allowed_appends (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → WGPrefix RoutingJoint.Event Int) (hn : ∀ ret, StateAppends (next ret)) :
    StateAppends (RoutingJoint.peerAllowedIps attrs peer pid next) := by
  unfold RoutingJoint.peerAllowedIps peerAllowedIpsWith
  repeat' first
    | (joint_append_head RoutingJoint.completedAllowedip; exact RoutingJoint.completed_appends _ _)
    | (joint_append_head RoutingJoint.peerConfigOut; exact RoutingJoint.access_appends _)
    | with_reducible exact hn _
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem tail_appends (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateAppends (RoutingJoint.peerConfigTail attrs peer pid) :=
  allowed_appends attrs peer pid _ (fun _ => RoutingJoint.access_appends _)

private theorem makeDead_appends (pid : PeerId) : StateAppends (RoutingJoint.makeDead pid) := by
  unfold RoutingJoint.makeDead peerMakeDeadWith
  repeat' first
    | (joint_append_head RoutingJoint.completedRemovePeer; exact RoutingJoint.completed_appends _ _)
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem remove_appends (peer : Option PeerId) : StateAppends (RoutingJoint.removePeer peer) := by
  unfold RoutingJoint.removePeer peerRemoveWith
  repeat' first
    | (joint_append_head RoutingJoint.makeDead; exact makeDead_appends _)
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem update_appends (remove : Option PeerId → WGPrefix RoutingJoint.Event Unit)
    (hr : ∀ peer, StateAppends (remove peer))
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateAppends (RoutingJoint.peerConfigUpdate remove attrs peer flags psk pid) := by
  unfold RoutingJoint.peerConfigUpdate peerConfigUpdateWith
  repeat' first
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.completedRemovePeer; exact RoutingJoint.completed_appends _ _)
    | (joint_append_head RoutingJoint.peerConfigOut; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.peerConfigTail; exact tail_appends _ _ _)
    | with_reducible exact hr _
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem acquired_appends (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) : StateAppends (RoutingJoint.peerCommandAcquired attrs key psk flags peer) := by
  unfold RoutingJoint.peerCommandAcquired peerCommandAcquiredWith
  repeat' first
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.peerConfigOut; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.peerConfigUpdate; exact update_appends _ remove_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

theorem setPeer_appends (attrs : PeerAttrs) : StateAppends (RoutingJoint.setPeerCommand attrs) := by
  unfold RoutingJoint.setPeerCommand setPeerCmdWith
  repeat' first
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.peerConfigOut; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.peerCommandAcquired; exact acquired_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem removeAll_appends : StateAppends RoutingJoint.removeAllPeers := by
  unfold RoutingJoint.removeAllPeers peerRemoveAllWith
  repeat' first
    | (joint_append_head RoutingJoint.completedFree; exact RoutingJoint.completed_appends _ _)
    | (joint_append_head RoutingJoint.makeDead; exact makeDead_appends _)
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem peers_appends (attrs : DeviceAttrs) : StateAppends (RoutingJoint.devicePeers attrs) := by
  unfold RoutingJoint.devicePeers devicePeersWith
  repeat' first
    | (joint_append_head RoutingJoint.setPeerCommand; exact setPeer_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem key_appends (attrs : DeviceAttrs) : StateAppends (RoutingJoint.deviceKey attrs) := by
  unfold RoutingJoint.deviceKey deviceKeyWith
  repeat' first
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.removePeer; exact remove_appends _)
    | (joint_append_head RoutingJoint.devicePeers; exact peers_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

private theorem deviceUpdate_appends (attrs : DeviceAttrs) (flags : UInt32) :
    StateAppends (RoutingJoint.deviceUpdate attrs flags) := by
  unfold RoutingJoint.deviceUpdate deviceUpdateWith
  repeat' first
    | (joint_append_head RoutingJoint.access; exact RoutingJoint.access_appends _)
    | (joint_append_head RoutingJoint.removeAllPeers; exact removeAll_appends)
    | (joint_append_head RoutingJoint.deviceKey; exact key_appends _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

theorem setDevice_appends (attrs : DeviceAttrs) : StateAppends (RoutingJoint.setDevice attrs) := by
  unfold RoutingJoint.setDevice setDeviceWith
  repeat' first
    | (joint_append_head RoutingJoint.deviceUpdate; exact deviceUpdate_appends _ _)
    | (joint_append_head ForIn.forIn; apply appends_forIn)
    | joint_append_step

theorem dispatchSet_appends (attrs : DeviceAttrs) : Appends (RoutingJoint.dispatchSet attrs) :=
  netlinkRequestWith_appends (setDevice_appends attrs).liftWGObserver

/-- A callback may emit arbitrary audit records and stop at any point. Its
actual joint append and RX projection rule out new consumed receipts, without
imposing any property on the old receipt history. -/
theorem audit_projection_checks (initial : FlatTable × FlatTable)
    {g : PrefixM RoutingJoint.Event α} {a : AuditM α}
    (appends : Appends g)
    (projection : ProjectsPrefix RoutingJoint.rxEvent id g (RxHistory.audit a))
    (w : World) (h : List RoutingJoint.Event) (hh : Checks initial h) :
    Checks initial (runPrefix g w h).2 := by
  obtain ⟨suffix,hs⟩ := appends w h
  have projected := congrArg Prod.snd (projection w h)
  let old := (h.filterMap RoutingJoint.rxEvent).filterMap RxHistory.auditEvent
  let extra := ((runPrefix a w old).2.drop old.length).map RxHistory.Event.audit
  change h.filterMap RoutingJoint.rxEvent ++ extra = _ at projected
  rw [hs,List.filterMap_append] at projected
  have newEvents := List.append_cancel_left projected
  rw [hs]
  apply hh.append
  intro pre event post position
  cases event with
  | routing completion => trivial
  | rx lower =>
    cases lower <;> try trivial
    case consumed occurrence id stamp receipt =>
      have member : RxHistory.Event.consumed occurrence id stamp receipt ∈
          suffix.filterMap RoutingJoint.rxEvent := by
        rw [position,List.filterMap_append]
        simp only [List.filterMap_cons,RoutingJoint.rxEvent,List.mem_append,List.mem_cons]
        exact Or.inr (Or.inl True.intro)
      rw [← newEvents] at member
      obtain ⟨audit,_,impossible⟩ := List.mem_map.mp member
      cases impossible

/-- Actual peer configuration retains earlier consume cuts and updates the
semantic routing state under the original input-address shape condition. -/
theorem setPeer (initial : FlatTable × FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial)
      (liftWGObserver (RoutingJoint.setPeerCommand attrs)) := by
  apply combine initial _ _ (setPeer_appends attrs).liftWGObserver
    ((RoutingJoint.setPeerCommand_routing attrs).liftWGObserver _ _)
    (setPeerCmdObserved_global initial attrs shape).liftWGObserver
  intro w h hi
  exact audit_projection_checks initial (setPeer_appends attrs).liftWGObserver
    (RoutingJoint.setPeerCommand_rx_product attrs) w h hi.2

/-- The real device configuration loop preserves the same positional journal;
individual peer shapes are precisely the existing device-shape premise. -/
theorem setDevice (initial : FlatTable × FlatTable) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial)
      (liftWGObserver (RoutingJoint.setDevice attrs)) := by
  apply combine initial _ _ (setDevice_appends attrs).liftWGObserver
    ((RoutingJoint.setDevice_routing attrs).liftWGObserver _ _)
    (wgSetDeviceObserved_global initial attrs shape).liftWGObserver
  intro w h hi
  exact audit_projection_checks initial (setDevice_appends attrs).liftWGObserver
    (RoutingJoint.setDevice_rx_product attrs) w h hi.2

/-- The concrete netlink dispatch retains normal errno and stopped-prefix
behavior through its actual socket, allocation and acknowledgement stages. -/
theorem dispatchSet (initial : FlatTable × FlatTable) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    PrefixPreserves (Inv initial) (Safe initial) (RoutingJoint.dispatchSet attrs) := by
  apply combine initial _ _ (dispatchSet_appends attrs)
    (RoutingJoint.dispatchSet_routing attrs)
    (dispatchObserved_global initial (.wgSet attrs) shape)
  intro w h hi
  exact audit_projection_checks initial (dispatchSet_appends attrs)
    (RoutingJoint.dispatchSet_rx attrs) w h hi.2

private theorem destruct_appends : StateAppends RoutingJoint.destructDevice := by
  unfold RoutingJoint.destructDevice destructWith
  apply StateAppends.bind (StateAppends.lift _)
  intro _
  apply StateAppends.bind (StateAppends.lift _)
  intro _
  exact removeAll_appends.bind (fun _ => RoutingJoint.access_appends _)

theorem dispatchCreate_appends : Appends RoutingJoint.dispatchCreate :=
  rtnetlinkRequestWith_appends (Appends.focus _ _ _)

theorem dispatchDelete_appends : Appends RoutingJoint.dispatchDelete :=
  rtnetlinkRequestWith_appends (envDeleteWith_appends
    (Appends.focus _ _ _) (Appends.focus _ _ _) destruct_appends.liftWGObserver)

/-- Creation changes the routing state through its actual return, while its
RX projection emits only audit events on both success and failure. -/
theorem dispatchCreate (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) RoutingJoint.dispatchCreate := by
  apply combine initial _ _ dispatchCreate_appends RoutingJoint.dispatchCreate_routing
    (dispatchObserved_global initial .wgCreate True.intro)
  intro w h hi
  exact audit_projection_checks initial dispatchCreate_appends
    RoutingJoint.dispatchCreate_rx w h hi.2

/-- Actual removal completions and the environment's early-error return keep
previous consume positions intact; no drain or residency premise is added. -/
theorem dispatchDelete (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) RoutingJoint.dispatchDelete := by
  apply combine initial _ _ dispatchDelete_appends RoutingJoint.dispatchDelete_routing
    (dispatchObserved_global initial .wgDelete True.intro)
  intro w h hi
  exact audit_projection_checks initial dispatchDelete_appends
    RoutingJoint.dispatchDelete_rx w h hi.2

end Leanux.Proofs.WG.RoutingPosition.Controls
