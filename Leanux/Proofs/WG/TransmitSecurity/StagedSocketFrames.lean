import Leanux.Proofs.WG.TransmitSecurity.StagedTimerFrames

/-! Endpoint and cache updates retain staged payloads and their peer allocation stamp. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "staged_socket_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head hiddenJiffies; unfold hiddenJiffies; exact hoare_liftAmbient _ _)
  | staged_exact_step $initial)

theorem cache_reset (pid : PeerId) : SameView stagedAt (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold dstCacheReset
  repeat' staged_socket_step initial

theorem cache_reset_now (pid : PeerId) : SameView stagedAt (dstCacheResetNow pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact cache_reset _ initial)
    | staged_socket_step initial

theorem clear_endpoint (pid : PeerId) : SameView stagedAt (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold clearPeerEndpointSrc
  repeat' first
    | (rx_retention_head dstCacheResetNow; exact cache_reset_now _ initial)
    | staged_socket_step initial

theorem endpoint (pid : PeerId) (e : Endpoint) : SameView stagedAt (setPeerEndpoint pid e) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold setPeerEndpoint requireNotPending endpointEq WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheReset; exact cache_reset _ initial)
    | staged_socket_step initial

theorem cache_set (pid : PeerId) (src gen dev : Nat) : SameView stagedAt (dstCacheSet pid src gen dev) :=
  update_peer pid (fun p => {p with dstCache := {p.dstCache with slot := some {src,gen,dev}}})
    (fun _ => ⟨rfl,rfl⟩)

theorem cache_get (pid : PeerId) (gen : Nat) : SameView stagedAt (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold dstCacheGet
  apply preserves_bind (hoare_liftAmbient (get : AmbientM Ambient) _)
  intro ambient
  apply preserves_bind (hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
  intro world
  split
  · exact preserves_pure _
  · apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
    intro peer
    let P := fun w => stagedAt w = initial ∧ stagedAt w pid = some (peer.internalId,peer.staged)
    apply hoare_consequence (P := P) (Q := fun _ => P) ?_ (fun _ hi => hi) (fun _ _ hi => hi.1)
    change Preserves P _
    have write (q : Peer) (same : q.internalId = peer.internalId ∧ q.staged = peer.staged) :
        Preserves P (setPeer pid q) := by
      simpa only [Preserves,P,same.1,same.2] using write_known (· = initial) pid q
    repeat' first
      | (rx_retention_head setPeer; apply write; exact ⟨rfl,rfl⟩)
      | (rx_retention_head hiddenJiffies; unfold hiddenJiffies; exact hoare_liftAmbient _ P)
      | rxstack_preserves_join
      | rx_retention_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
