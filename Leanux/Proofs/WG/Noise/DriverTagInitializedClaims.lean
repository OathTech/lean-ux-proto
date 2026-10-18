import Leanux.Proofs.WG.Noise.DriverTagRunnerClaims
import Leanux.Proofs.WG.Noise.DriverTagSyscallSource

/-! Concrete initialized claims. The original runner supplies initialization,
dispatch, result serialization and indexed Stops; only its normal final
WireGuard state and completed tag journal are projected here. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.WholeDriver
open Lean Leanux Leanux.Runner

def inspection (trace : Trace) (placeholders : Bool) : Initialized.Inspection :=
  Initialized.inspection Syscalls.syscall trace placeholders

theorem facts (trace : Trace) (placeholders : Bool) :
    Initialized.Facts (inspection trace placeholders) :=
  Initialized.facts Syscalls.syscall (Syscalls.syscall_preserves Initialized.emptyTags)
    trace placeholders

theorem erases (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders :=
  Initialized.inspection_json Syscalls.syscall Syscalls.syscall_erases trace placeholders

theorem normal (trace : Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Snapshot)
    (returned : (inspection trace placeholders).1 = .ok (json,final)) :
    HandshakeTags final.tagAt ∧
      ∀ pid tag, final.tagAt pid = some tag →
        ∃ event ∈ (inspection trace placeholders).2, EventValid event ∧ event.Effect ∧
          event.after.tagAt pid = some tag :=
  (facts trace placeholders).normal_summary returned

end Leanux.Proofs.WG.Noise.DriverTags.WholeDriver
