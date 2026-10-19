import Leanux.Proofs.WG.Roaming.RemoteChronologyOriginModel
import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerSource
import Leanux.Proofs.WG.Roaming.RemoteChronologyClassificationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

/-- The selected setter occurs at this position in the original driver
journal, and no later setter or allocation reset affects this peer. -/
def LatestOrigin.Valid (trace : Runner.Trace) (placeholders : Bool)
    (pid : PeerId) (remote : Remote) (q : LatestOrigin) : Prop :=
  ∃ before event after,
    RemoteDriver.Runner.history trace placeholders = before ++ event :: after ∧
    q.position = before.length ∧
    Driver.effect event pid = some (some remote) ∧
    Untouched Driver.effect after pid ∧
    RemoteProvenance.Matches trace placeholders [event] q.origin ∧
    (match q.origin with
     | .data record _ => record.position = (before.filterMap RemoteDriver.rxEvent).length
     | _ => True)

end Leanux.Proofs.WG.Roaming.RemoteChronology
