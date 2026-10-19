import Leanux.Proofs.WG.Progress.TimerHookSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected recorded-suffix guarantees for actual timer arming and receive
hooks. These preserve normal-return suffixes, not whole-worker termination. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem armTimer_record_suffix (records : List HiddenRecord) (peer : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Campaign2.Ensures (armTimer peer timer delay caller)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (armTimer_retains records peer timer delay caller g)
    a (value,after) b (pre ▸ tail_self records) run

theorem timersDataReceived_record_suffix (records : List HiddenRecord) (peer : PeerId) :
    Campaign2.Ensures (timersDataReceived peer)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (timersDataReceived_retains records peer g)
    a (value,after) b (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
