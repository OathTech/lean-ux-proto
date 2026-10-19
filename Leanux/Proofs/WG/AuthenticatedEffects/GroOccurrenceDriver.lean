import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! Concrete native-stack specialization. The neutral equality rewrites the
refined native poll to the existing arbitrary-batch poll and stackFlush source,
so existing neutral journal contracts need no new transport proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def withStack (hooks : Driver.Hooks E)
    (scope : GroOccurrence.Entry → PrefixM E Unit → PrefixM E Unit)
    (pid : PeerId) (budget : Nat) : PrefixM E Nat :=
  observed (fun action => liftWGObserver (liftWGPrefix action))
    hooks.candidateEnter hooks.candidateLeave hooks.counterCheck
    (fun peer packet endpoint => liftWGObserver (Driver.consumeObserved hooks peer packet endpoint))
    scope (Driver.stackObserved hooks) pid budget

theorem nativePoll_neutral (hooks : Driver.Hooks E) (pid : PeerId) (budget : Nat) :
    withStack hooks (fun _ body => body) pid budget =
      Driver.pollObserved hooks pid budget (Driver.stackFlushObserved hooks) :=
  observed_neutral _ _ _ _ _ _ pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
