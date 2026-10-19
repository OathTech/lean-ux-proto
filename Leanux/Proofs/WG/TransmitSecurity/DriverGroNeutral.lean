import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! Neutral stack-input observation recovers the original native batch callback
exactly, including stopped prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem nativePoll_neutral (hooks : Hooks E)
    (neutral : hooks.stackInput = fun _ body => body) (pid : PeerId) (budget : Nat) :
    nativePollObserved hooks pid budget = pollObserved hooks pid budget (stackFlushObserved hooks) := by
  unfold nativePollObserved
  rw [neutral]
  exact AuthenticatedEffects.GroOccurrencePoll.observed_neutral _ _ _ _ _ _ pid budget

end Leanux.Proofs.WG.TransmitSecurity.Driver
