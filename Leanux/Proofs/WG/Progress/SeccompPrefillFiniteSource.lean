import Leanux.Proofs.WG.Progress.SeccompProgramFiniteSource
import Leanux.Seccomp.Prefill
/-! Exact Prefill source equations. Keep the native creator fixed in the
program-parametric bridge before substituting its finite counterpart; this
avoids reducing the closed fixture while checking definitional equality. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompPrefillFinite
open Leanux Leanux.Seccomp
def translatedWith
    (create : SockFprog → Local.L (Except Int Seccomp.BpfProg))
    (p : Seccomp.ClassicProg) : Except String Seccomp.BpfProg :=
  Prefill.translated.match_1 (motive := fun _ => Except String Seccomp.BpfProg)
    (Local.run (create { len := p.size, filter := some p }) {})
    (fun prog _ => .ok prog)
    (fun err _ => .error s!"seccomp_prefill: the mirror's checker rejects the prefill program ({err})")
    (fun stop => .error s!"seccomp_prefill: the translation stopped: {stop.message}")
def translated : Except String Seccomp.BpfProg :=
  translatedWith SeccompLocalProgramFinite.create Prefill.program
theorem translatedWith_source (p : Seccomp.ClassicProg) :
    translatedWith (bpfProgCreateFromUser : SockFprog → Local.L (Except Int Seccomp.BpfProg)) p =
      translatedWith SeccompLocalProgramFinite.create p :=
  congrArg (fun create => translatedWith create p)
    (funext SeccompLocalProgramFinite.create_source)

def nativeGeneric (p : Seccomp.ClassicProg) : Except String Seccomp.BpfProg :=
  match Local.run (bpfProgCreateFromUser { len := p.size, filter := some p }) {} with
  | .ok (.ok prog, _) => .ok prog
  | .ok (.error err, _) => .error s!"seccomp_prefill: the mirror's checker rejects the prefill program ({err})"
  | .error stop => .error s!"seccomp_prefill: the translation stopped: {stop.message}"
theorem native_bridge : Prefill.translated = nativeGeneric Prefill.program := rfl
theorem generic_finite (p : Seccomp.ClassicProg) : nativeGeneric p =
    translatedWith SeccompLocalProgramFinite.create p := translatedWith_source p
theorem translated_source : Prefill.translated = translated :=
  native_bridge.trans (generic_finite Prefill.program)


/-- Original prefill context with only the translation result exposed. The
count guard precedes that result, and all filter/task updates are unchanged. -/
def installWith (translation : Except String Seccomp.BpfProg)
    (n : Nat) (sc : SeccompWorld) (t : TaskWorld) :
    Except String (SeccompWorld × TaskWorld) := do
  if n == 0 || n > Prefill.PREFILL_MAX then
    throw s!"seccomp_prefill: {n} copies (1..{Prefill.PREFILL_MAX})"
  let prog ← translation
  let mut k := sc
  let mut prev : Option FilterId := none
  for _ in [0:n] do
    let id := k.nextFilter
    let flt : SeccompFilter := {
      id := id
      allowNative := Prefill.allowNative
      prev := prev
      prog := prog.toKernel
      origProg := Prefill.program.map SockFilter.toKernel }
    k := { k with nextFilter := id + 1, filters := k.filters.insert id flt }
    prev := some id
  let task : Task := { t.task with
    noNewPrivs := true
    seccomp := { mode := .filter, filterCount := n, filter := prev } }
  return (k, { t with task })

theorem install_factor (n : Nat) (sc : SeccompWorld) (t : TaskWorld) :
    Prefill.apply n sc t = installWith Prefill.translated n sc t := rfl

/-- Finite translation followed by the native bounded copy/cache context. -/
def install := installWith translated

theorem install_source : Prefill.apply = install := by
  funext n sc t
  rw [install_factor, translated_source]
  rfl

end Leanux.Proofs.WG.Progress.SeccompPrefillFinite
