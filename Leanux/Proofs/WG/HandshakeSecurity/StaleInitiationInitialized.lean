import Leanux.Proofs.WG.HandshakeSecurity.StaleInitiationFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalInitialized

/-! Stale-input refusal at the actual completed native consumer receipt in the
initialized final journal. The stale premise is solely the actual parser's
timestamp comparison; no refusal, freshness invariant or accepted-history
premise is supplied. Native H1 exchange frame packages remain explicit. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open AuthenticatedEffects CausalJournal

theorem initialized_native (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.consumeInitiation msg r) :: post) :
    r.Valid (consumeInitiation msg) := by
  have history := ExchangeCausal.initialized facts config traffic trace placeholders
  apply (history.checked (pre.filterMap exchange?) (post.filterMap exchange?)
    (.consumeInitiation msg r) ?_).1
  rw [position,List.filterMap_append,List.filterMap_cons]
  rfl

theorem initialized_refusal (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.consumeInitiation msg r) :: post)
    (stale : Stale msg r.before r.ambientBefore) :
    r.value = none ∧ PeerBorrow.view r.after = PeerBorrow.view r.before ∧
      r.after.sent = r.before.sent :=
  original_quiet msg r (initialized_native facts config traffic trace placeholders
    pre post msg r position) stale

/-- The actual initialized stale consumer makes the native receive handler
return at its no-peer refusal branch. Its suffix performs no response creation,
session installation, timer operation or transmission. -/
theorem initialized_no_response (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.consumeInitiation msg r) :: post)
    (stale : Stale msg r.before r.ambientBefore) (src : SkbSource) (loaded : Bool)
    (entry : Ambient) (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (ambient : r.ambientBefore = initiationConsumerEntry loaded entry) :
    ((Cookies.afterMac msg src loaded (authenticatedMac loaded)).run r.before).run entry =
      .ok (((),r.after),CounterWindow.record r.ambientAfter .hsInitNoPeer true) ∧
      PeerBorrow.view r.after = PeerBorrow.view r.before ∧ r.after.sent = r.before.sent :=
  receiver_returns_at_refusal msg src loaded r entry kind ambient
    (initialized_native facts config traffic trace placeholders pre post msg r position) stale

end Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
