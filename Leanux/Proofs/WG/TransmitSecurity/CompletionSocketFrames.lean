import Leanux.Proofs.WG.TransmitSecurity.CompletionSocketSource
import Leanux.Proofs.WG.AuthenticatedEffects.SentFrames

/-! Cache and loopback bookkeeping cannot append a WireGuard datagram; the
actual send's final tunnel append is treated separately. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes AuthenticatedEffects
set_option maxHeartbeats 600000

private theorem cacheReset (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (dstCacheReset pid) := by
  have frame : SameView WGWorld.sent (dstCacheReset pid) := by
    sent_frame [dstCacheReset,getPeer,setPeer,getAmbient,hiddenJiffies] using []
  exact frame.wp P

private theorem cacheGet (P : List SentDatagram → Prop) (pid : PeerId) (gen : Nat) :
    Preserves (fun w => P w.sent) (dstCacheGet pid gen) := by
  have frame : SameView WGWorld.sent (dstCacheGet pid gen) := by
    sent_frame [dstCacheGet,getPeer,setPeer,getAmbient,hiddenJiffies] using []
  exact frame.wp P

private theorem cacheSet (P : List SentDatagram → Prop) (pid : PeerId) (src gen dev : Nat) :
    Preserves (fun w => P w.sent) (dstCacheSet pid src gen dev) := by
  have frame : SameView WGWorld.sent (dstCacheSet pid src gen dev) := by
    sent_frame [dstCacheSet,getPeer,setPeer] using []
  exact frame.wp P

private theorem loopback (P : List SentDatagram → Prop) (sites : List HiddenSite) (raised : Bool) :
    Preserves (fun w => P w.sent) (loopbackSend sites raised) := by
  have frame : SameView WGWorld.sent (loopbackSend sites raised) := by
    sent_frame [loopbackSend,loopbackSoftirq,raiseLoopbackRx,getAmbient,peekHiddenSite] using []
    all_goals
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi run
      cases run
  exact frame.wp P

theorem tunnelFront_sent (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) :
    SameView WGWorld.sent (tunnelFront e bytes r exactRx) := by
  sent_frame [tunnelFront] using [loopback,socketPort_sent_spec]

theorem socket4Front_sent (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : SameView WGWorld.sent (socket4Front e cache bytes ds exactRx) := by
  sent_frame [socket4Front,socket4AfterCacheFront,socket4MissFront,socket4RetryFront,
    socket4RouteFront,socket4FinishFront,send4ClearSrcSource,getPeer,setPeer] using [cacheGet,cacheReset,cacheSet]

theorem socket6Front_sent (e : Endpoint) (cache : Option PeerId) :
    SameView WGWorld.sent (socket6Front e cache) := by
  sent_frame [socket6Front,getPeer,setPeer] using [cacheGet,cacheReset,cacheSet]

end Leanux.Proofs.WG.TransmitSecurity.Completion
