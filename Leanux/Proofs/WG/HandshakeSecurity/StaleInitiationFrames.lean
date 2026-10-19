import Leanux.Proofs.WG.HandshakeSecurity.StaleInitiationSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeQuietFrames

/-! A stale original consumer restores all peer records, including their
timers and session state. The full native handler returns at its refusal arm,
before response creation, endpoint changes or handshake timer effects. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open AuthenticatedEffects Lifetimes Cookies CounterWindow

theorem original_quiet (msg : Key) (r : WGRunWitness (Option PeerId))
    (valid : r.Valid (consumeInitiation msg))
    (stale : Stale msg r.before r.ambientBefore) :
    r.value = none ∧ PeerBorrow.view r.after = PeerBorrow.view r.before ∧
      r.after.sent = r.before.sent := by
  have rejected := original_refuses msg r.before r.after r.ambientBefore r.ambientAfter
    r.value stale valid
  have run := valid
  change ((consumeInitiation msg).run r.before).run r.ambientBefore =
    .ok ((r.value,r.after),r.ambientAfter) at run
  rw [rejected] at run
  exact ⟨rejected,
    initiation_refusal_restores_peers msg r.before r.after r.ambientBefore r.ambientAfter run,
    (ProjectedAction.iff_run_ambient _ _ _).mp (consumeInitiation_sent msg)
      r.before r.ambientBefore none r.after r.ambientAfter run⟩

theorem receiver_returns_at_refusal (msg : Key) (src : SkbSource) (loaded : Bool)
    (r : WGRunWitness (Option PeerId)) (entry : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (ambient : r.ambientBefore = initiationConsumerEntry loaded entry)
    (valid : r.Valid (consumeInitiation msg))
    (stale : Stale msg r.before r.ambientBefore) :
    ((afterMac msg src loaded (authenticatedMac loaded)).run r.before).run entry =
      .ok (((),r.after),record r.ambientAfter .hsInitNoPeer true) ∧
      PeerBorrow.view r.after = PeerBorrow.view r.before ∧ r.after.sent = r.before.sent := by
  obtain ⟨rejected,peers,sent⟩ := original_quiet msg r valid stale
  have run := valid
  change ((consumeInitiation msg).run r.before).run r.ambientBefore =
    .ok ((r.value,r.after),r.ambientAfter) at run
  rw [rejected,ambient] at run
  exact ⟨afterMac_initiation_refused msg src loaded r.before r.after entry r.ambientAfter kind run,
    peers,sent⟩

end Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
