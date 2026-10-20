# Campaign 2: original Prefill specialization blocker

Update, 2026-10-20: the proposed staged bridge is adopted and integrated, together
with whole prefill and trace initialization. The current status and validation
are in the [campaign report](2026-10-14-proof-campaign-2.md); the investigation
and earlier failed form below remain historical evidence.

## Investigation update, 2026-10-20

The [staged-bridge investigation](2026-10-20-proof-campaign-2-prefill-investigation.md)
now proves the exact previously rejected equality at the stock limits,
with standard axioms and fresh kernel replay. The isolated failure was the
native closed-definition bridge, not specializing the generic creator
equation. The tested fix separates those two equalities and composes them.
It remains a proposed integration, outside the registered proof tree; H5
global termination is still unproved. The following sections record the
original failed proof form and its stopping decision.

## Historical status after the shared carry

Main 3308c49a is merged into proofs/campaign-2 at a9845661. One stock-limit
reproduction after that merge still rejects the closed Prefill specialization.
H5 global termination is unproved. This is a proof-form blocker, not a
counterexample to termination or a new mirror request. The shared carry
removes the former traffic dependencies; concrete traffic/syscall/Runner
composition has not yet been completed. The merge carry itself is validated:
the full gate passes 3,119 jobs and 1,761 terminal statements with standard
axioms only, fresh whole-tree kernel replay exits zero, and all 12 existing
counterexample recipes pass. These checks exclude the rejected specialization
and do not establish H5 global termination.

[USER 2026-10-19] If this specialization remains blocked after the merge,
report its declaration and limit and stop without a workaround. No option,
resource cap, mirror definition or statement domain is changed. Work after
the reproduction is limited to completing and validating the merge carry.

## Exact declaration and limit

The rejected declaration is:

```lean
Leanux.Proofs.WG.Progress.SeccompPrefillFinite.translated_source :
  Leanux.Seccomp.Prefill.translated =
    Leanux.Proofs.WG.Progress.SeccompPrefillFinite.translated
```

The native target is Leanux.Seccomp.Prefill.translated at
Leanux/Seccomp/Prefill.lean:54. It specializes the Local creator to
Prefill.program, the closed 3,990-instruction program. The proposed right
side specializes the already-checked finite Local creator to that same
program. The generic creator equation is accepted; its closed specialization
is rejected by the kernel.

Toolchain: Lean v4.35.0. The effective maxRecDepth is **512**, with no local
or package override. The toolchain source defines defaultMaxRecDepth as 512
in Init/Prelude.lean:4980, uses it for the option in
Lean/Util/RecDepth.lean:15, and passes maxRecDepth.get opts to the kernel
in Lean/AddDecl.lean:28.

The one post-merge probe exits **1** with:

```text
<stdin>:23:8: error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit
```

The diagnostic's suggested option change is not applied. There is no rerun,
limit increase, alternate specialization or accepted closed theorem.

## Reproduction

Run the following source through:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean --stdin
```

This is the exact tested source, including the separate generic and reflexive
controls. It intentionally fails and is not part of the trusted proof tree.

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

theorem translated_source : Prefill.translated = translated :=
  translatedWith_source Prefill.program
#print axioms translatedWith_source
#print axioms translated_source
end Leanux.Proofs.WG.Progress.SeccompPrefillFinite
```

The generic audit reports only propext, Classical.choice and Quot.sound.
The diagnostic print after the rejected closed theorem additionally names
translated_source itself. That is a rejected placeholder, not a successful
axiom audit or a checked theorem. No probe source, compiled object or log is
installed in the proof tree. The campaign report retains the earlier failed
architectures and resource outcomes; this single post-merge probe introduces
no new resource failure.
