import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.JitterExhaustionSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.RetrySource
import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Every successful jitter draw returns fewer than HZ/3 ticks and leaves
all kernel state unchanged. This normal-completion contract does not characterize errors. -/
theorem source_jitter_bound (site : HiddenSite) (initial : Kernel) :
    Ensures (jitterBelowRekeyTimeout site) (fun w => w.k = initial)
      (fun n w => w.k = initial ∧ n < HZ / 3) :=
  (ensures_iff _ _ _).mpr (jitter_bounded (· = initial) site)

/-- A normally completed original initiation-send prefix preserves the peer's
allocation identity, retry-attempt count, reference count and retransmit expiry.
This includes message construction, MAC, traversal, socket/cache/accounting
updates and the original early exits; the retransmit arm hook follows it. -/
theorem source_initiation_prefix_frame (pid : PeerId) (identity attempts refs : Nat)
    (expiry : Option UInt64) :
    Ensures (initiationArmPrefix pid)
      (fun w => initiationAt w pid = some (identity, attempts, refs, expiry))
      (fun _ w => initiationAt w pid = some (identity, attempts, refs, expiry)) :=
  (ensures_iff _ _ _).mpr (initiationArmPrefix_view pid (identity, attempts, refs, expiry))

/-- Original initiation sending preserves peer identity, retry attempts and
references whenever it returns normally. Its final hook may change the
retransmit expiry. A normal return does not assert transmission success. -/
theorem source_handshake_send_frame (pid : PeerId) (identity attempts refs : Nat) :
    Ensures (sendHandshakeInitiation pid)
      (fun w => workerAt w pid = some (identity, attempts, refs))
      (fun _ w => workerAt w pid = some (identity, attempts, refs)) :=
  sendHandshakeInitiation_workerView pid (identity, attempts, refs)

end Leanux.Proofs.WG.TimerDiscipline
