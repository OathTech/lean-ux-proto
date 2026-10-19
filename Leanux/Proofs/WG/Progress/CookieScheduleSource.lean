import Leanux.Proofs.WG.Progress.CookieScheduleLeaves
import Leanux.Proofs.WG.Progress.CookieScheduleOutcomeSource
import Leanux.Proofs.WG.Progress.CookieScheduleFrames

/-! Exact bounded schedule factors and the unrestricted original scheduler loop.
The retired totality predictions are refuted statements, not type-given frames. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.Env

-- turn_stop is refuted by the bad-tail activation invariant and the checked
-- schedule_cookieBadTail_completes (CookieScheduleFindings).
-- turn_yield is refuted by turn_cookieHole_counterexample
-- (CookieScheduleSupportFindings): nonempty logical items do not force a live
-- physical head. cookieScheduler_run retains the actual turn and its errors.

def schedulerLoop (turns : List Nat) : Leanux.M (Option Unit × Unit) :=
  forIn turns (none,()) (fun _ _ => scheduleTurn none)

-- schedulerLoop_run predicted unconditional completion, already refuted on its
-- first turn by the same bad-tail input. The definition above retains arbitrary
-- supplied turns. schedule_run factors the actual schedule and its remainder;
-- it is not a retyping of the retired arbitrary-turn totality theorem.

end Leanux.Proofs.WG.Progress.CookieFull
