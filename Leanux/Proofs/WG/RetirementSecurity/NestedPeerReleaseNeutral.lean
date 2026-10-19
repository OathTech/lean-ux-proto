import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseErasure
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral

/-! Exact neutral specialization of the exposed nested repayment calls. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

theorem lifted_erases : Ops.Erases (lifted : Ops (WGPrefix E)) where
  step := erasesStatePrefix_lift
  release := fun _ => erasesStatePrefix_lift _

theorem initiationOut_lifted (peer ret : Option PeerId) :
    initiationOutWith (lifted : Ops (WGPrefix E)) peer ret = liftWGPrefix (initiationOutWith native peer ret) :=
  TimerEffects.eq_native_lift (initiationOut_erases lifted_erases peer ret)
    (initiationOut_frame some (lifted_frames some) peer ret)

theorem initiationTail_lifted (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    initiationTailWith (lifted : Ops (WGPrefix E)) msg e ck hash peer pid = liftWGPrefix (initiationTailWith native msg e ck hash peer pid) :=
  TimerEffects.eq_native_lift (initiationTail_erases lifted_erases msg e ck hash peer pid)
    (initiationTail_frame some (lifted_frames some) msg e ck hash peer pid)

theorem initiationCheck_lifted (msg : Key) :
    initiationCheckWith (lifted : Ops (WGPrefix E)) msg = liftWGPrefix (initiationCheckWith native msg) :=
  TimerEffects.eq_native_lift (initiationCheck_erases lifted_erases msg)
    (initiationCheck_frame some (lifted_frames some) msg)

theorem responseTail_lifted (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    responseTailWith (lifted : Ops (WGPrefix E)) msg identity pid = liftWGPrefix (responseTailWith native msg identity pid) :=
  TimerEffects.eq_native_lift (responseTail_erases lifted_erases msg identity pid)
    (responseTail_frame some (lifted_frames some) msg identity pid)

theorem responseCheck_lifted (msg : Key) :
    responseCheckWith (lifted : Ops (WGPrefix E)) msg = liftWGPrefix (responseCheckWith native msg) :=
  TimerEffects.eq_native_lift (responseCheck_erases lifted_erases msg)
    (responseCheck_frame some (lifted_frames some) msg)

theorem cookieAfter_lifted (pid : PeerId) (cookie : Option Key) :
    cookieAfterWith (lifted : Ops (WGPrefix E)) pid cookie = liftWGPrefix (cookieAfterWith native pid cookie) :=
  TimerEffects.eq_native_lift (cookieAfter_erases lifted_erases pid cookie)
    (cookieAfter_frame some (lifted_frames some) pid cookie)

theorem cookie_lifted (msg : Key) :
    cookieWith (lifted : Ops (WGPrefix E)) msg = liftWGPrefix (cookieWith native msg) :=
  TimerEffects.eq_native_lift (cookie_erases lifted_erases msg)
    (cookie_frame some (lifted_frames some) msg)

theorem clear_lifted (pid : PeerId) :
    clearWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (clearWith native pid) :=
  TimerEffects.eq_native_lift (clear_erases lifted_erases pid)
    (clear_frame some (lifted_frames some) pid)

theorem flushedClear_lifted (pid : PeerId) :
    flushedClearWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (flushedClearWith native pid) :=
  TimerEffects.eq_native_lift (flushedClear_erases lifted_erases pid)
    (flushedClear_frame some (lifted_frames some) pid)

theorem cleanup_lifted (skb : SkbId) (pkt : RxPacket) (flag : Bool) :
    cleanupWith (lifted : Ops (WGPrefix E)) skb pkt flag = liftWGPrefix (cleanupWith native skb pkt flag) :=
  TimerEffects.eq_native_lift (cleanup_erases lifted_erases skb pkt flag)
    (cleanup_frame some (lifted_frames some) skb pkt flag)

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
