import Leanux.Proofs.WG.Progress.SeccompProgramFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Complete concrete outcomes of migration, preparation and creation. Native
claims use the campaign projection; Local claims retain its whole result/state.
No successful conversion, install, prefill or initialized-run premise appears,
and no such larger caller is concluded. A Stop carries no invented final state. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompProgramFinite
open Leanux Leanux.Seccomp

theorem original_migrate_finite (insns orig : Seccomp.ClassicProg) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (bpfMigrateFilter insns orig)) (liftSeccomp (migrate insns orig)) := by
  rw [migrate_source]
  intro w pre
  rfl

theorem original_prepare_finite (insns orig : Seccomp.ClassicProg) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (bpfPrepareFilter insns orig)) (liftSeccomp (prepare insns orig)) := by
  rw [prepare_source]
  intro w pre
  rfl

theorem original_create_finite (fprog : Seccomp.SockFprog) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftSeccomp (bpfProgCreateFromUser fprog)) (liftSeccomp (create fprog)) := by
  rw [create_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.SeccompProgramFinite

namespace Leanux.Proofs.WG.Progress.SeccompLocalProgramFinite
open Leanux Leanux.Seccomp

theorem original_migrate_result_finite (insns orig : Seccomp.ClassicProg)
    (initial : Local.LState) :
    Local.run (bpfMigrateFilter insns orig : Local.L _) initial =
      Local.run (migrate insns orig) initial := by
  rw [migrate_source]

theorem original_prepare_result_finite (insns orig : Seccomp.ClassicProg)
    (initial : Local.LState) :
    Local.run (bpfPrepareFilter insns orig : Local.L _) initial =
      Local.run (prepare insns orig) initial := by
  rw [prepare_source]

theorem original_create_result_finite (fprog : Seccomp.SockFprog)
    (initial : Local.LState) :
    Local.run (bpfProgCreateFromUser fprog : Local.L _) initial =
      Local.run (create fprog) initial := by
  rw [create_source]

end Leanux.Proofs.WG.Progress.SeccompLocalProgramFinite
