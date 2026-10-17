import Leanux.Proofs.WG.Cookies.Load
import Leanux.Proofs.Logged.Advance

/-! Original cookie exclusion under load, beside the accepted retry-limit
counterexample. These declarations do not assert a universal retry-episode
bound or kernel reachability of the generated replay. -/
namespace Leanux.Proofs.WG.FloodResistance
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.KeyTimes Leanux.Proofs.Logged

/-- The original queue threshold produces under-load=true and stores the
actual recorded coarse clock; no saved-decay premise is required. -/
theorem original_under_load_queue (w u : WGWorld) (a b : Ambient) (d : Device) (now : Int64)
    (hd : w.dev = some d)
    (hq : d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hc : (((hiddenClock64 .underLoadNow : WG.M Int64).run w).run
      (recordCmp a .hsUnderLoad true (Int.ofNat d.handshakeQueueLen)
        (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8)))) = .ok ((now, u), b)) :
    (loadPhase.run w).run a = .ok ((true, {u with lastUnderLoad := some now}), b) :=
  load_queue w u a b d now hd hq hc

/-- Below the queue threshold, the actual saved-load clock keeps load active
exactly on this unexpired branch. The signed deadline includes wrap. -/
theorem original_under_load_decay (w u : WGWorld) (a b : Ambient) (d : Device) (last now : Int64)
    (hd : w.dev = some d)
    (hq : ¬d.handshakeQueueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
    (hl : w.lastUnderLoad = some last)
    (hc : (((hiddenClock64 .birthdateExpired : WG.M Int64).run w).run
      (record (recordCmp a .hsUnderLoad false (Int.ofNat d.handshakeQueueLen)
        (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8))) .hsWasUnderLoad true)) =
      .ok ((now, u), b))
    (hn : ¬deadline last 1 ≤ now) :
    (loadPhase.run w).run a = .ok ((true, u),
      recordCmp b .hsDecayExpired false (deadline last 1).toInt now.toInt) :=
  load_decay w u a b d last now hd hq hl hc hn

/-- An initiation with an actual under-load run, valid MAC1 and invalid MAC2
against the actual make_cookie result executes precisely the cookie-reply
suffix. This equality retains its complete WG/Ambient result and any later Stop.
The selected original suffix has no Noise consume/create call. -/
theorem original_invalid_mac2_cookie_only (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION) (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (replyEntry h.checked) :=
  receive_rejected_run msg src w a ht h

/-- Every ordinary completion of that rejected initiation preserves complete
peer/keypair stores, indices, static identity, device frontiers and both global
peer/keypair counters. Only cookie secret/birthdate and TX statistics are
removed from the device view. Both original make_cookie calls may rotate;
IPv4/IPv6 and ordinary socket failures are included. -/
theorem original_invalid_mac2_noise_preserved (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION) (h : FailedMac2 msg src w a)
    (hr : ((receiveHandshakePacket msg src).run w).run a = .ok (((), v), b)) :
    noiseView v = noiseView w := receive_rejected_frame msg src w v a b ht h hr

/-- Invalid MAC1 takes the original drop before cookie creation or Noise,
independently of MAC2. The actual under-load prefix and resident device are
explicit, and the complete Noise view is preserved. -/
theorem original_invalid_mac1_drop (msg : List UInt8) (src : SkbSource)
    (w u : WGWorld) (a b : Ambient) (d : Device)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (hl : (loadPhase.run w).run (record a .hsCookie false) = .ok ((true, u), b))
    (hd : u.dev = some d) (hm : mac1Computed d msg ≠ mac1Given msg) :
    ((receiveHandshakePacket msg src).run w).run a =
        .ok (((), u), dropEntry (record b .macInvalid true)) ∧
      noiseView u = noiseView w := by
  have hr := receive_bad_mac1 msg src w u a b d ht hl hd hm
  exact ⟨hr, receive_bad_mac1_frame msg src w u u a b _ d ht hl hd hm hr⟩

/-- The advance observer used by the retry and time replays preserves the
whole original syscall result, successful World and Stop. Recorded timer
units are observed; the placeholder path is lifted without a unit-coverage
claim. -/
theorem original_advance_observer_erasure (ticks : Nat) :
    ErasesPrefix (advanceSyscallObserved ticks) (syscall (.wgAdvance ticks)) :=
  advanceSyscallObserved_erases ticks

end Leanux.Proofs.WG.FloodResistance
