import Leanux.Proofs.WG.HandshakeSecurity.Frames
import Leanux.Proofs.WG.HandshakeSecurity.ReplayClaims
import Leanux.Proofs.WG.HandshakeSecurity.StopClaims
import Leanux.Proofs.WG.HandshakeSecurity.Increasing
import Leanux.Proofs.WG.HandshakeSecurity.ConsumerRefusal
import Leanux.Proofs.WG.HandshakeSecurity.WorkerClaims

/-! T4's local timestamp tranche. Initialized retained-peer histories and the
connection from the compared value to the preceding successful consumption
remain separate obligations; these statements do not claim campaign completion. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The original initiation consumer emits only actual timestamp writes whose
received value exceeds the value used by its timestamp comparison. Its exact
normal result or Stop is preserved, and receipts before Stop remain covered.
This is a native-call claim, not an initialized retained-peer history theorem. -/
theorem original_initiation_timestamp_receipts (msg : List UInt8)
    (w : WGWorld) (a : Ambient) :
    (runWGPrefix (consumeObserved msg) w a []).1 =
      ((consumeInitiation msg).run w).run a ∧
    SoundReceipts (runWGPrefix (consumeObserved msg) w a []).2 := by
  refine ⟨consume_erases msg w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := consume_sound msg w a [] (by intro r h; cases h)
  exact safe

/-- Every recorded initiation timestamp write changes exactly the timestamp
in the retained peer's handshake projection, preserving its allocation identity,
handshake material, tag and key slots at that write. -/
theorem original_initiation_written_projection (msg : List UInt8)
    (w : WGWorld) (a : Ambient) (r : TimestampReceipt)
    (occurs : r ∈ (runWGPrefix (consumeObserved msg) w a []).2) :
    r.Newer ∧ ∃ p,
      peerView r.execution.before r.peer = some (handshakeView p) ∧
      peerView r.execution.after r.peer =
        some { handshakeView p with timestamp := r.received } := by
  obtain ⟨valid, newer⟩ := (original_initiation_timestamp_receipts msg w a).2 r occurs
  exact ⟨newer, receipt_written_view r valid⟩

/-- The original timestamp-write arm cannot overwrite peer state with a value
that fails its strict comparison. This local guard statement excludes the
surrounding consumer's reference release and is not full replay rejection. -/
theorem original_stale_timestamp_arm (pid : PeerId) (old t : List UInt8)
    (w : WGWorld) (a : Ambient) (stale : memcmp t old ≠ .gt) :
    ((timestampStep pid old t).run w).run a =
      .ok (((), w), CounterWindow.record a .consumeNewerTimestamp false) :=
  stale_timestamp_step pid old t w a stale

/-- A stale decrypted initiation timestamp takes the original refusal suffix,
returns no peer and preserves every surviving peer's handshake and freshness
projection. Cleanup may delete a peer. This source-cut claim starts at the
actual comparison; transport from initialized execution remains separate. -/
theorem original_stale_initiation_suffix (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) (p : Peer) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (stale : memcmp t p.latestTimestamp ≠ .gt)
    (run : ((checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p).run w).run a =
      .ok ((result, v), b)) :
    result = none ∧ RetainsHandshake w v :=
  checked_stale_result msg e ck hash t peer pid p w v a b result stale run

/-- Every committed timestamp write in the original initiation consumer is
strictly newer than that peer's actual pre-write timestamp, including receipts
before a later Stop. This local native-call result has no supplied coherence
or freshness invariant; initialized lifetime history remains a separate claim. -/
theorem original_initiation_timestamp_increases (msg : List UInt8)
    (w : WGWorld) (a : Ambient) :
    IncreasingReceipts (runWGPrefix (consumeObserved msg) w a []).2 := by
  obtain ⟨_, _, safe, _⟩ := consume_increasing msg w a [] (by intro r h; cases h)
  exact safe

/-- A normally rejected original initiation cannot change a surviving peer's
handshake material, freshness state or key slots. This includes the real
public-key lookup and reference cleanup; deletion is permitted. The result is
local to the consumer, so queue, load and outer receive effects are separate. -/
theorem original_initiation_refusal_retains (msg : List UInt8) (w v : WGWorld)
    (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none, v), b)) :
    RetainsHandshake w v := original_none_retains msg w v a b run

/-- Every timestamp receipt committed by the original handshake receive worker
records a real write strictly newer than that peer's actual prior timestamp.
The observer preserves the worker's full normal result or Stop and retains
receipts before failure. This is worker transport, not initialized lifetime
history or a claim about unobserved fixture operations. -/
theorem original_worker_timestamp_increases (w : WGWorld) (a : Ambient) :
    (runWGPrefix Worker.observed w a []).1 = (receiveStep.run w).run a ∧
    IncreasingReceipts (runWGPrefix Worker.observed w a []).2 := by
  refine ⟨Worker.erases w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := Worker.increasing w a [] (by intro r h; cases h)
  exact safe

end Leanux.Proofs.WG.HandshakeSecurity
