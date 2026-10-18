import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeferred

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem removeByPeer_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (removeByPeer pid) := by
  apply native_fields (pool_of_material (removeByPeer_material pid))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact (CurrentSlots.Removal.listDel_fields _).wp (fun s => s = initial))
    | (rx_retention_head AllowedIps.removeNodeBody
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotRemoval.«0».Leanux.Proofs.WG.CurrentSlots.Removal.node_fields)
         (removeNodeBody_sameNode _)).wp (fun s => s = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec CurrentSlots.fields (fun s => s = initial)
       intro x b
       change Preserves (fun w => CurrentSlots.fields w = initial) _)
    | slot_fields_step initial

theorem makeDead_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact removeByPeer_native _ confirmed)
    | responder_handshake_step confirmed

theorem afterDead_native (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch, unsupported, invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact keypairsClear_native H1 _ confirmed)
    | (rx_retention_head timersStop; exact stopTimers_native H1 _ confirmed)
    | (rx_retention_head drainHandshakeSendWq; exact drain_native H1 _ confirmed)
    | responder_handshake_step confirmed

theorem remove_native (H1 : H1ResponderCurrentEdges) (peer : Option PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact makeDead_native _ confirmed)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead_native H1 _ confirmed)
    | responder_handshake_step confirmed

theorem freeAips_native (confirmed : List Nat) : Preserves (History.Native confirmed) WG.free := by
  apply native_fields ?_ CurrentSlots.Removal.free_fields
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have projected := congrArg (fun s : WGStoreView × (PeerId → Option Peer) => pool {dev := s.1.dev}) kept
  funext kid
  have projectedAt := congrFun projected kid
  simpa only [pool, AllowedIps.clearStoreView, AllowedIps.clearStoreProjection,
    AllowedIps.resetAllowedips, wgStoreView, Option.map_map, Option.map_bind,
    Option.bind_map, Function.comp_def] using projectedAt

theorem removeAll_native (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Preserves (History.Native confirmed) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact freeAips_native confirmed)
    | (rx_retention_head peerMakeDead; exact makeDead_native _ confirmed)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead_native H1 _ confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (History.Native confirmed)
       intro x b
       change Preserves (History.Native confirmed) _)
    | responder_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
