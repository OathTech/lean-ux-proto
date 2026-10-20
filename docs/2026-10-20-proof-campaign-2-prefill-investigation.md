# Campaign 2: Prefill proof-factoring investigation

## Recommendation and scope

The exact equality rejected on 2026-10-19 now checks with the stock Lean
v4.35.0 limits. Use the small staged source bridge below. It retains the
original statement, including every success, checker error and Local Stop;
it changes neither the mirror nor the finite creator. There is no reason
from this investigation to raise a Lean limit or introduce a new termination
framework.

This is an investigation over campaign checkpoint e901e03d / mirror
3308c49a. The successful prototype is reproduced here, outside the registered
proof tree; integrating it and completing H5 have not resumed. H5 global
termination remains unproved. The earlier [blocker report](2026-10-19-proof-campaign-2-prefill-blocker.md)
remains the record of the rejected proof form.

[USER 2026-10-20] Investigate the obstruction and alternative routes, then
return recommendations before continuing the campaign. Changes to Lean
limits are a last resort; the existing memory cap remains unchanged.

## What failed, and what works

The closed specialization of the generic creator equation already succeeds:
translatedWith_source Prefill.program is accepted at maxRecDepth 512.
The isolated failure is the definitional-equality bridge from the native
Prefill.translated constant to the callback-parametric wrapper. Thus the
previous description of a failed closed specialization was too broad.

The successful proof separates two jobs:

1. Fix the original creator in a program-parametric native wrapper. Its
   body is the actual native match, including its default Local state and
   error text. Reflexivity connects Prefill.translated to this wrapper at
   Prefill.program.
2. While the program remains a variable, use the existing generic creator
   equality to substitute the finite creator. Instantiate that theorem and
   compose the two equalities by transitivity.

The measured kernel reducibility heights are native Prefill.translated =
21, callback-parametric translatedWith = 8, nativeGeneric = 21, and the
closed finite translated = 23. Lean v4.35.0's Lean/Declaration.lean:17–45
explains that lazy delta reduction unfolds the higher regular definition
first and unfolds equal-height heads together. These observations support
unfolding order as the cause: the original bridge exposes the closed
translation before the surrounding expressions line up. The staged bridge
lets their common context line up first. No internal kernel reduction trace
was collected, so this is a supported explanation, not a measured call stack.
The fix does not set heights or change transparency attributes.

## Checked prototype

This source is the successful NaturalMatch probe. All three named bridge
and final theorem audits report only propext, Classical.choice and Quot.sound.
Compilation takes under one second on this box; this is an observation,
not a timing requirement. Compiling the same prototype to an olean and
running leanchecker --fresh NaturalMatch both exit zero. No warning or
non-standard axiom appears in the successful prototype.

```lean
import Leanux.Proofs.WG.Progress.SeccompProgramFiniteSource
import Leanux.Seccomp.Prefill
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
example : Prefill.translated = Prefill.translated := rfl

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
#print axioms native_bridge
#print axioms generic_finite
#print axioms translated_source
end Leanux.Proofs.WG.Progress.SeccompPrefillFinite
```

To reproduce, save the code as
.tmp/c2-prefill-investigation/NaturalMatch.lean, then run:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -R .tmp/c2-prefill-investigation -o .tmp/c2-prefill-investigation/NaturalMatch.olean .tmp/c2-prefill-investigation/NaturalMatch.lean
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env python3 - <<'PYREPLAY'
from pathlib import Path
import os, subprocess, sys
scratch = Path('.tmp/c2-prefill-investigation').resolve()
env = dict(os.environ)
env['LEAN_PATH'] = str(scratch) + os.pathsep + env.get('LEAN_PATH', '')
sys.exit(subprocess.run(['leanchecker', '--fresh', 'NaturalMatch'], env=env).returncode)
PYREPLAY
```

## Experiments and alternatives

The original failed theorem and its separate native reflexivity bridge both
reproduce the kernel-recursion failure. The closed generic specialization,
a literal native copy and a checked exact declaration-copy control pass.
The ordinary staged bridge passes, as does its readable match-syntax form
above. The proposed solution uses no metaprogrammed declaration. Three
initial diagnostic helpers failed on ordinary form errors (a missing Repr
instance, an ambiguous BpfProg name and the CommandElabM/CoreM boundary);
the corrected helpers pass. No audit printed after a rejected declaration
is counted as an accepted theorem.

Requesting the generated Prefill.translated.eq_def equation started expensive
computation: the diagnostic process used about 17 GB RSS after 25 seconds.
It was deliberately stopped at its verified owned PID; capped reports KILLED,
exit 143. This is a failed diagnostic, not a pass or an infrastructure rerun.
No memory cap or Lean parameter was raised. The earlier high-limit failure
is recorded in the campaign report and was not repeated.

| Route | Assessment |
| --- | --- |
| Staged source bridge | Recommended: exact original equality checks, ordinary proof terms, unchanged limits and existing architecture. |
| Explicit finite-execution certificate for the native Prefill call | Could retain full scope, but requires a sound certificate interface; leaving the call opaque or citing its Lean type alone would not prove runtime termination. More work than the checked bridge. |
| Concrete translation certificate checked in chunks | Possible fallback, but ties the proof to this large fixture and requires a checked connection to the native computation. Unnecessary here. |
| Larger recursion limit or generated eq_def | Not recommended: the historical high-limit probe and the new equation-generation diagnostic both start expensive closed computation. |
| Exclude Prefill or assume its result | Would narrow the initialized Runner claim; unnecessary and not recommended. |

Two independent read-only reviews found no semantic weakening or trust
expansion in the staged bridge. Neither review ran probes or edited files.

## Proposed continuation

After approval to resume, integrate the staged bridge in an owned Progress
source module. Next connect all of Prefill.apply to the finite translation,
retaining its 1..8 count guard, filter insertion order and task updates.
Program construction, the NR_syscalls cache scan, its program.size + 1
interpreter budget, and the copy loop are already bounded in the native
source; they remain part of the finite-evaluation justification.

Carry that result through RunnerBoundarySource.runnerInitial, preserving
Env.seccompPrefill's exact (0, Stop.invariant e) error mapping and the
subsequent optional network initialization. Reuse executeTrace_boundary_source
for the runner composition. Concrete traffic and syscall finite composition,
and the separate dispatched/resumed-work and accepted-endpoint progress
claims, still need completion. This prototype closes one source equation;
it proves neither whole H5 termination nor successful Prefill installation.
