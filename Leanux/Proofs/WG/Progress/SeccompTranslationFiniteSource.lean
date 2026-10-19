import Leanux.Proofs.WG.Progress.SeccompProgramFiniteSource
import Leanux.Seccomp.Engine

/-! Exact finite evaluation of the executable translation comparison. The
original bounded classic and eBPF engines are unchanged; agreement is not
assumed, and rejection, Stop and disagreement are preserved. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompTranslationFinite
open Leanux Leanux.Seccomp

/-- The executable translation comparison has the same Local creation seam;
both bounded engines and all original result cases are retained. -/
def checkWith
    (create : Seccomp.SockFprog → Local.L (Except Int Seccomp.BpfProg))
    (p : Seccomp.ClassicProg) (d : Seccomp.SeccompData) : TranslationCheck :=
  match Local.run (create { len := p.size, filter := some p }) with
  | .error stop => .stopped stop
  | .ok (.error e, _) => .rejected e
  | .ok (.ok prog, _) =>
    let c := classicRun p d
    let e := BpfEngine.run MiniInterp.mk prog d
    if c == e then .agree c else .disagree c e

theorem check_factor (p : Seccomp.ClassicProg) (d : Seccomp.SeccompData) :
    checkTranslation p d = checkWith (bpfProgCreateFromUser : Seccomp.SockFprog → Local.L (Except Int Seccomp.BpfProg)) p d := by
  rfl

def check (p : Seccomp.ClassicProg) (d : Seccomp.SeccompData) : TranslationCheck :=
  checkWith SeccompLocalProgramFinite.create p d

theorem check_source (p : Seccomp.ClassicProg) (d : Seccomp.SeccompData) :
    checkTranslation p d = check p d := by
  rw [check_factor]
  unfold check
  have create : (fun f => (bpfProgCreateFromUser f : Local.L _)) =
      SeccompLocalProgramFinite.create := by
    funext f
    exact SeccompLocalProgramFinite.create_source f
  exact congrArg (fun callback => checkWith callback p d) create

end Leanux.Proofs.WG.Progress.SeccompTranslationFinite
