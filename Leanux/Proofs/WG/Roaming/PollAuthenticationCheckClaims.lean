import Leanux.Proofs.WG.Roaming.PollAuthenticationCheckSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes PublicationIdentity
open Origins.HistorySupport (sessions)

/-- Every projected check has prior authentication, whether or not its
enclosing consume or initialized runner subsequently completes. -/
theorem initialized_checks_authenticated (trace : Runner.Trace) (placeholders : Bool) :
    ∀ q ∈ checks trace placeholders,
      ∃ e : Authentication, e.Valid trace placeholders q ∧ e.Facts q :=
  fun q member => check_authenticated trace placeholders q
    ((check_mem_iff trace placeholders q).mp member)

/-- Every original reached check is represented, at its exact history index. -/
theorem initialized_checks_complete (trace : Runner.Trace) (placeholders : Bool)
    (q : Check) (occurs : q.Occurs trace placeholders) :
    q ∈ checks trace placeholders :=
  (check_mem_iff trace placeholders q).mpr occurs

/-- The projection retains the original JSON or indexed Stop exactly. -/
theorem inspection_outcome (trace : Runner.Trace) (placeholders : Bool) :
    (inspection trace placeholders).outcome = Runner.executeTrace trace placeholders :=
  RxHistory.executeTraceHistory_erases trace placeholders []

theorem inspection_authenticated (trace : Runner.Trace) (placeholders : Bool) :
    ∀ q ∈ (inspection trace placeholders).checks,
      ∃ e : Authentication, e.Valid trace placeholders q ∧ e.Facts q :=
  initialized_checks_authenticated trace placeholders

theorem inspection_complete (trace : Runner.Trace) (placeholders : Bool) (q : Check) :
    q ∈ (inspection trace placeholders).checks ↔ q.Occurs trace placeholders :=
  check_mem_iff trace placeholders q


end Leanux.Proofs.WG.Roaming.PollAuthentication
