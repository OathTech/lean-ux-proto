import Leanux.Proofs.WG.RetirementSecurity.KeySlotPublication

/-! Existing native configured-field and holder-field frames jointly retain
exactly the dead bit and published slots. This factors cached timer/socket
writes without assuming equality of the whole peer or world. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem combined (configured : ConfiguredIdentity.view v=ConfiguredIdentity.view w)
    (points : ownershipPointView v=ownershipPointView w) : view v=view w := by
  funext pid
  have dead := congrArg (fun s=>s.bind fun state=>(state.peers pid).map ConfiguredIdentity.Cell.dead) configured
  have slots := congrFun (congrArg (fun s=>s.2.2.1) points) pid
  have deadEq : (peerAt v pid).map Peer.isDead=(peerAt w pid).map Peer.isDead := by
    simpa only [ConfiguredIdentity.view,ConfiguredIdentity.state,ConfiguredIdentity.cell,
      peerAt,Option.bind_map,Option.map_bind,Function.comp_def,Option.map_map] using dead
  have slotEq : (peerAt v pid).map peerOwnership=(peerAt w pid).map peerOwnership := slots
  cases hv : peerAt v pid <;> cases hw : peerAt w pid
  all_goals simp only [hv,hw,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at deadEq slotEq
  all_goals try contradiction
  · simp [view,hv,hw]
  · simp only [view,hv,hw,Option.map_some,Option.some.injEq,cell]
    exact Prod.ext deadEq (congrArg Prod.fst slotEq)

theorem combined_frame {action : WG.M α}
    (configured : SameView ConfiguredIdentity.view action)
    (points : SameView ownershipPointView action) : Preserves (InvExcept pending) action := by
  apply frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact combined ((ProjectedAction.iff_run_ambient _ _ _).mp configured w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp points w a result v b run)

theorem initiation (pid : PeerId) : Preserves (InvExcept pending) (sendHandshakeInitiation pid) :=
  combined_frame (ConfiguredHandshake.sendHandshakeInitiation_view pid) (HolderHandshake.initiation_points pid)

theorem create_response (pid : PeerId) : Preserves (InvExcept pending) (createResponse pid) :=
  combined_frame (ConfiguredReceive.createResponse_view pid) (HolderHandshake.create_response_points pid)

theorem add_mac (pid : PeerId) (msg : List UInt8) : Preserves (InvExcept pending) (addMacToPacket pid msg) :=
  combined_frame (ConfiguredHandshake.addMacToPacket_view pid msg) (HolderHandshake.add_mac_points pid msg)

theorem buffer (pid : PeerId) (msg : List UInt8) : Preserves (InvExcept pending) (sendBufferToPeer pid msg) :=
  combined_frame (ConfiguredHandshake.sendBufferToPeer_view pid msg) (HolderHandshake.buffer_points pid msg)

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    Preserves (InvExcept pending) (armTimer pid timer delay jc) :=
  combined_frame (ConfiguredIdentity.armTimer_view pid timer delay jc) (armTimer_ownership pid timer delay jc)

theorem del_timer (pid : PeerId) (timer : PeerTimer) : Preserves (InvExcept pending) (delTimer pid timer) :=
  combined_frame (ConfiguredIdentity.delTimer_view pid timer) (delTimer_ownership pid timer)

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (InvExcept pending) (modPeerTimer site pid timer delay) :=
  combined_frame (ConfiguredIdentity.modPeerTimer_view site pid timer delay) (modPeerTimer_ownership site pid timer delay)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
