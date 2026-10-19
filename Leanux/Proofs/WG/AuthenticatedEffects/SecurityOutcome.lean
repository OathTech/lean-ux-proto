import Leanux.Proofs.WG.AuthenticatedEffects.CookieCheckedIsolation
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalFullInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.MacWorldFrames
import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendAuthorization
import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCookieFinal
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCookieAmplification
import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryFinal
import Leanux.Proofs.WG.AuthenticatedEffects.Frames
import Leanux.Proofs.WG.AuthenticatedEffects.MacRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.DecryptEffects
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceCookieInitialized
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceInitiationRefusal
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceResponseKeys

/-! Initialized authenticated effects, occurrence-specific egress and refusal
records on the same final Driver. The component types keep their projections
visible. MAC/decrypt refusal frames and the all-entry cookie-only receive factor
remain explicit source contracts; no whole-world equality or
bound on the number of adversarial input occurrences is claimed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev FinalHistory (trace : Runner.Trace) (placeholders : Bool) :=
  (runPrefixOuter (CausalJournal.execute trace placeholders) []).2

/-- T3 component claims on one actual initialized driver. Each field names an actual occurrence or
an exact history predicate. Entry funding, replay coherence, packet provenance
and causal-root well-formedness are conclusions of initialization. -/
structure SecurityOutcome (trace : Runner.Trace) (placeholders : Bool) : Prop where
  appends : ∀ before after append,
    (runPrefixOuter (RawAppend.execute trace placeholders) []).2 = before ++ append :: after →
    ∃ pre event post, FinalHistory trace placeholders = pre ++ event :: post ∧
      pre.filterMap RawAppend.Final.raw? = before ∧ RawAppend.Final.raw? event = some append ∧
      post.filterMap RawAppend.Final.raw? = after ∧
      CausalJournal.Emissions.added event = [append.datagram] ∧
      CausalJournal.Emissions.AuthorizedAppend pre event
  effects : ∀ before after event, FinalHistory trace placeholders = before ++ event :: after →
    CausalJournal.Coverage.Protected event → CausalJournal.Roots.Rooted before
  handshake : HandshakeFresh.Safe ((FinalHistory trace placeholders).filterMap CausalJournal.handshake?)
  transport : TransportReplay.Safe CausalJournal.StackOrigins.origin? CausalJournal.StackOrigins.replay?
    (FinalHistory trace placeholders)
  stack : ∀ before after index entry,
    FinalHistory trace placeholders = before ++ .scope (.entered ⟨index,.stackInput entry⟩) :: after →
    CausalJournal.Roots.AuthenticatedReceive entry.scope entry.skb entry.packet before
  cookie : ∀ before after receipt,
    FinalHistory trace placeholders = before ++ .cookieSocket receipt :: after →
    receipt.Valid ∧ receipt.Qualifying ∧ receipt.datagram.bytes.length < receipt.input.length
  cookieCount : ∀ msg source w loaded checked a b c (history : List CausalJournal.Event),
    messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE →
    (Cookies.loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((true,loaded),b) →
    ((cookieValidatePacket msg source true).run loaded).run b = .ok ((.noCookie,checked),c) →
    ∃ suffix, (runWGPrefix (RawAppend.Final.receiver CausalJournal.hooks.session
      (TransmitSecurity.Driver.keepaliveObserved CausalJournal.hooks) msg source) w a history).2.filterMap RawAppend.Final.raw? =
      history.filterMap RawAppend.Final.raw? ++ suffix ∧ suffix.length ≤ 1
  cookieIsolation : ∀ msg source w loaded checked v a b c d,
    messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE →
    (Cookies.loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((true,loaded),b) →
    ((cookieValidatePacket msg source true).run loaded).run b = .ok ((.noCookie,checked),c) →
    ((receiveHandshakePacket msg source).run w).run a = .ok (((),v),d) →
    Cookies.noiseView v = Cookies.noiseView w
  macRefusal : ∀ msg source loaded state w u v a b c,
    messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE →
    (Cookies.loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((loaded,u),b) →
    ((cookieValidatePacket msg source loaded).run u).run b = .ok ((state,v),c) →
    state = .invalid ∨ state = .ratelimited →
    ((receiveHandshakePacket msg source).run w).run a = .ok (((),v),invalidDropEntry loaded c) ∧
      MacWorld.view v = MacWorld.view w
  decrypt : ∀ packet result w v a b,
    ((decryptPacket packet).run w).run a = .ok ((result,v),b) →
    v = w ∨ result = none ∧ ∃ device key c,
      w.dev = some device ∧ device.keypairs[packet.keypair]? = some key ∧
      ((KeyTimes.receiveReject key).run w).run (CounterWindow.record a .decNoKeypair false) =
        .ok ((true,w),c) ∧
      v = CounterWindow.store w packet.keypair {key with receiving := {key.receiving with isValid := false}}
  initiationRefusal : ∀ before after msg (receipt : WGRunWitness (Option PeerId)),
    FinalHistory trace placeholders = before ++ .exchange (.consumeInitiation msg receipt) :: after →
    receipt.value = none →
    RefusalOutside.full receipt.after = RefusalOutside.full receipt.before
  responseRefusal : ∀ before after msg (receipt : WGRunWitness (Option PeerId)),
    FinalHistory trace placeholders = before ++ .exchange (.consumeResponse msg receipt) :: after →
    receipt.value = none →
    RefusalOutside.full receipt.after = RefusalOutside.full receipt.before
  cookieRefusal : ∀ before after (receipt : CookieConsumption.Receipt),
    FinalHistory trace placeholders = before ++ .cookieConsumed receipt :: after →
    (runWGPrefix (acceptedCookie receipt.input) receipt.run.before receipt.run.ambientBefore []).2 = [] →
    RefusalOutside.full receipt.run.after = RefusalOutside.full receipt.run.before
  replayRefusal : ∀ before after (receipt : ReplayEntry.Event),
    FinalHistory trace placeholders = before ++ .old (.replay receipt) :: after →
    receipt.run.value = false →
    ReplayRefusal.view receipt.run.after.wg = ReplayRefusal.view receipt.run.before.wg

/-- Security: initialized protocol effects and every original append have their
own accepted-input or fixture cause; delayed actions inherit exact earlier
occurrences, cookie replies remain the bounded source-qualified exception, and
refused consumers/replay checks retain the complete named protocol projections.
The claim permits stopped outer executions and assumes no incoming invariant. -/
theorem initialized_authenticated_effects (trace : Runner.Trace) (placeholders : Bool) :
    SecurityOutcome trace placeholders where
  appends := RawAppend.Final.initialized_authorized trace placeholders
  effects := CausalJournal.Roots.initialized trace placeholders
  handshake := HandshakeFresh.initialized_final trace placeholders
  transport := CausalJournal.StackOrigins.initialized_replays trace placeholders
  stack := CausalJournal.StackOrigins.initialized_authenticated trace placeholders
  cookie := CausalJournal.Receipts.initialized_cookie_size trace placeholders
  cookieCount := RawAppend.Final.checked_receiver_count
  cookieIsolation := CookieChecked.isolation
  macRefusal := MacWorld.refused
  decrypt := decryptPacket_effect
  initiationRefusal := RefusalOutside.final_initiation trace placeholders
  responseRefusal := RefusalOutside.final_response trace placeholders
  cookieRefusal := RefusalOutside.final_cookie trace placeholders
  replayRefusal := ReplayEntry.final_refusal trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects
