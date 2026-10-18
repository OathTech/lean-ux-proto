import Leanux.Proofs.WG.AuthenticatedEffects.BorrowedRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalEmission

/-! Full initiation-refusal composition. The masked fields are exactly cookie
secret maintenance and the two rate-limit tables; every peer record is retained
pointwise, including timers, with no reference-count hypothesis. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Cookies Leanux.Proofs.WG.CounterWindow

def quietCookieStore (s : WGStoreView) : WGStoreView :=
  {s with dev := s.dev.map cookieDevice, ratelimiter := {s.ratelimiter with table := [],table6 := []}}

def quietPeerStore (s : WGStoreView) : WGStoreView × (PeerId → Option Peer) :=
  (PeerBorrow.outsidePeers (quietCookieStore s),PeerBorrow.resident s)

def handshakeQuietView (w : WGWorld) := quietPeerStore (wgStoreView w)

theorem quietPeerStore_factor (s : WGStoreView) :
    quietPeerStore s = (quietCookieStore (PeerBorrow.outsidePeers s),PeerBorrow.resident s) := by
  simp only [quietPeerStore,quietCookieStore,PeerBorrow.outsidePeers,cookieDevice,
    Option.map_map,Function.comp_def]

theorem cookieValidatePacket_quiet (msg : List UInt8) (src : SkbSource) (loaded : Bool) :
    SameView handshakeQuietView (cookieValidatePacket msg src loaded) := by
  apply (cookieValidatePacket_sameCookie msg src loaded).of_factor
    (fun s : WGOwnedView => (PeerBorrow.outsidePeers s.toWGStoreView,PeerBorrow.resident s.toWGStoreView))
  intro w
  simp only [handshakeQuietView,quietPeerStore,quietCookieStore,cookieView,wgOwnedView,wgStoreView]
  apply Prod.ext
  · rfl
  · funext pid
    change (w.dev.bind fun d => d.peers[pid]?) = ((w.dev.map cookieDevice).bind fun d => d.peers[pid]?)
    cases w.dev <;> rfl

theorem initiation_refusal_quiet (msg : List UInt8) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none,v),b)) :
    handshakeQuietView v = handshakeQuietView w := by
  have restored := initiation_refusal_restores_peers msg w v a b run
  have masked := congrArg (fun pair : WGStoreView × (PeerId → Option Peer) =>
    (quietCookieStore pair.1,pair.2)) restored
  simpa only [handshakeQuietView,quietPeerStore_factor,PeerBorrow.view] using masked

theorem receive_initiation_refused_quiet (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeInitiation msg).run q).run (initiationConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsInitNoPeer true) ∧
      handshakeQuietView v = handshakeQuietView w ∧ v.sent = w.sent := by
  have loadFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (loadPhase_sameStore.factor quietPeerStore) w _ loaded u b load
  have macFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieValidatePacket_quiet msg src loaded) u b _ q c mac
  have noiseFrame := initiation_refusal_quiet msg q v _ d refused
  have emitted := receive_initiation_refused_sent msg src loaded w u q v a b c d kind load mac refused
  exact ⟨emitted.1,noiseFrame.trans (macFrame.trans loadFrame),emitted.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects
