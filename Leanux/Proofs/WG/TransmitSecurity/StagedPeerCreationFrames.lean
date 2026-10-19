import Leanux.Proofs.WG.Queues.ConfigurationPhysical
import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames

/-! Peer creation introduces an empty staged queue. Metadata initialization
retains the exact queue read from the native peer, without a fresh-slot premise. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem write_empty_peer (pid : PeerId) (peer : Peer) (empty : peer.staged = []) :
    Preserves (Inv h) (setPeer pid peer) := by
  have same : {peer with staged := []} = peer := by cases peer; simp_all
  simpa only [same] using clear_staged (h:=h) pid peer

private theorem precompute_staged (pid : PeerId) : SameView stagedAt (precomputeStaticStatic pid) := by
  intro initial
  unfold precomputeStaticStatic requireNotPending
  simp only [pure_bind]
  apply preserves_bind ((Exact.store getDev_sameWGStore).wp (· = initial))
  intro device
  apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
  intro peer
  let P := fun w => stagedAt w = initial ∧ stagedAt w pid = some (peer.internalId,peer.staged)
  apply hoare_consequence (P := P) (Q := fun _ => P) ?_ (fun _ before => before) (fun _ _ before => before.1)
  change Preserves P _
  simp only [branch]
  repeat' first
    | (receive_update_head setPeer
       apply (Exact.update_peer _ _ ?_).wp (fun q => q = initial ∧ q pid = some (peer.internalId,peer.staged))
       intro p
       exact ⟨rfl,rfl⟩)
    | (rx_retention_head setPeer; exact Exact.write_known (· = initial) pid _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem precompute (pid : PeerId) : Preserves (Inv h) (precomputeStaticStatic pid) :=
  frame (epoch_rx_ring ((pinned_const _private.Leanux.Proofs.WG.Queues.ConfigurationPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical.precompute_cell) pid))
    (Staged.of_view _ (precompute_staged pid))

theorem handshake_init (pid : PeerId) (psk : Option Key) : Preserves (Inv h) (handshakeInit pid psk) := by
  unfold handshakeInit IndexOwner.setPeerWord
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | (rx_retention_head setKeypair; exact write_key _ _)
    | staged_origin_native

theorem reset_handshake (pid : PeerId) : Preserves (Inv h) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake hiddenClock64
  repeat' staged_origin_native

theorem cache_reset (pid : PeerId) : Preserves (Inv h) (dstCacheReset pid) :=
  exact_ring (RxRing.dstCacheReset_cell pid) (Exact.cache_reset pid)

theorem peer_create (key : Key) (psk : Option Key) : Preserves (Inv h) (peerCreate key psk) := by
  unfold peerCreate
  simp only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head setPeer; exact write_empty_peer _ _ rfl)
    | (rx_retention_head handshakeInit; exact handshake_init _ _)
    | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
    | staged_origin_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
