import Leanux.Proofs.WG.AuthenticatedEffects.DecryptWorkerFrames

/-! Native send-free frames for timer and handshake bookkeeping. Actual
socket senders are intentionally excluded and need their append receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem delete (pid : PeerId) (timer : PeerTimer) : SameView WGWorld.sent (delTimer pid timer) := by
  sent_frame [delTimer] using [getPeer_sent_spec,setPeer_sent_spec]

theorem place (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    SameView WGWorld.sent (placeOnWheel pid timer expires clock unit) := by
  sent_frame [placeOnWheel,peekHiddenSite] using [getPeer_sent_spec,setPeer_sent_spec]
  all_goals
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b hi run
    cases run

theorem place_spec (P : List SentDatagram → Prop) (pid : PeerId) (timer : PeerTimer)
    (expires clock : UInt64) (unit : Option Nat) :
    Preserves (fun w => P w.sent) (placeOnWheel pid timer expires clock unit) :=
  (place pid timer expires clock unit).wp P

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView WGWorld.sent (armTimer pid timer delay caller) := by
  sent_frame [armTimer,getAmbient] using [getPeer_sent_spec,place_spec]
  all_goals
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b hi run
    cases run

theorem guard (pid : PeerId) : SameView WGWorld.sent (modPeerTimerGuard pid) := by
  sent_frame [modPeerTimerGuard] using [getPeer_sent_spec]

theorem endpoint (pid : PeerId) (src : SkbSource) :
    SameView WGWorld.sent (setPeerEndpointFromSkb pid src) := by
  sent_frame [setPeerEndpointFromSkb,endpointFromSkb,setPeerEndpoint,dstCacheReset,
    requireNotPending,endpointEq,getAmbient,hiddenJiffies]
    using [getPeer_sent_spec,setPeer_sent_spec]

theorem completed (pid : PeerId) (site : HiddenSite) :
    SameView WGWorld.sent (timersHandshakeComplete pid site) := by
  sent_frame [timersHandshakeComplete,delTimer] using [getPeer_sent_spec,setPeer_sent_spec]

theorem mac (pid : PeerId) (msg : Key) : SameView WGWorld.sent (addMacToPacket pid msg) := by
  sent_frame [addMacToPacket,getPeer,setPeer,branchExpired,birthdateTest] using []

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
