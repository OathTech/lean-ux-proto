import Leanux.Proofs.WG.RetirementSecurity.RxCompletionFrames

/-! Confirmation allocates no packet cells. Endpoint and completion-timer
bookkeeping retain the packet frontier needed by the actual staged send. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits StagingOccurrences

private theorem geometry_store {action : WG.M α} (same : SameWGStore action) :
    SameView geometry action :=
  same.of_factor (fun store => geometry {dev := store.dev}) geometry (fun _ => rfl)

theorem endpoint_geometry (pid : PeerId) (endpoint : Endpoint) :
    SameView geometry (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact (geometry_store (endpointEq_sameStore _ _)).wp (· = initial))
    | staging_geometry_step initial

theorem delTimer_geometry (pid : PeerId) (timer : PeerTimer) :
    SameView geometry (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold delTimer
  repeat' staging_geometry_step initial

theorem handshakeComplete_geometry (pid : PeerId) (site : HiddenSite) :
    SameView geometry (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_geometry _ _).wp (· = initial))
    | staging_geometry_step initial

theorem confirmation_geometry (pid : PeerId) (kid : KeypairId) :
    SameView geometry (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch,modifyPeer_source]
  repeat' first
    | (rx_retention_head keypairPut; exact (key_put_geometry _ _).wp (· = initial))
    | staging_geometry_step initial

theorem geometry_bound {action : WG.M α} (same : SameView geometry action) :
    Preserves Packets.Inv action := (same.factor Prod.fst).wp Bounded

end Leanux.Proofs.WG.RetirementSecurity
