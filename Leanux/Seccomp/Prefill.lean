import Leanux.Seccomp.Bridge
import Leanux.Seccomp.Local

/-!
# The seccomp prefill fixture

`"seccomp_prefill": N` (contracts/trace-v1.md; docs/2026-10-12-seccomp-design.md
section 5) [USER 2026-10-12: queued]: before the window, the
guest sets no-new-privs and installs `N` copies of the fixed program below
(harness/guest.c, `SECCOMP_PREFILL_*`). The mirror's initial task state carries
that chain, reconstructed here by the mirror's own translation of the same
program under the record-free local instance, and the cache bitmap by the
decision-free constant-allow emulation: an environment assumption (`Env.lean`,
`seccompPrefill`), not a modelled path, since the installs happen outside
every window and leave no record. The program loads `nr`, branches to a long
`JA` chain only for a dummy number outside the probe set and the cached range,
and returns `ALLOW` otherwise, so every probed number is a cache hit through
the chain. Its point is the path budget: eight copies (3995 eBPF instructions
each, 3999 with the walk's penalty) leave `seccomp_attach_filter` 776
instructions short of `MAX_INSNS_PER_PATH`, which one recorded install can
reach or cross (corpus/seccomp `s_budget_*`).
-/

namespace Leanux.Seccomp.Prefill

/-- The program's classic length and the dummy number (never cached: above
    462; never called: outside the probe set). The guest holds the same
    constants. -/
def PREFILL_LEN : Nat := 3990
def PREFILL_DUMMY_NR : UInt32 := 100000
/-- The most copies the fixture installs: the ninth would itself exceed the
    budget (9 × 3999 > 32768). -/
def PREFILL_MAX : Nat := 8

def program : ClassicProg := Id.run do
  let mut p : ClassicProg := #[stmt (BPF_LD ||| BPF_W ||| BPF_ABS) 0,
                               jump (BPF_JMP ||| BPF_JEQ ||| BPF_K) PREFILL_DUMMY_NR 1 0,
                               stmt (BPF_RET ||| BPF_K) SECCOMP_RET_ALLOW]
  for _ in [0:PREFILL_LEN - 4] do
    p := p.push (stmt (BPF_JMP ||| BPF_JA) 0)
  return p.push (stmt (BPF_RET ||| BPF_K) SECCOMP_RET_ALLOW)

/-- The chain's `allow_native`, as `seccomp_cache_prepare` computes it from
    all-ones (the first filter) or the previous bitmap (identical here):
    computed by the decision-free emulation, not assumed. -/
def allowNative : BitVec NR_syscalls := Id.run do
  let mut b := BitVec.allOnes NR_syscalls
  for nr in [0:NR_syscalls] do
    if !seccompIsConstAllowPure program (Int.ofNat nr) AUDIT_ARCH_X86_64 then
      b := b &&& ~~~(1#NR_syscalls <<< nr)
  return b

/-- The translated program, by the mirror's translation with no records. -/
def translated : Except String BpfProg :=
  match Local.run (bpfProgCreateFromUser { len := program.size, filter := some program }) {} with
  | .ok (.ok p, _) => .ok p
  | .ok (.error e, _) => .error s!"seccomp_prefill: the mirror's checker rejects the prefill program ({e})"
  | .error stop => .error s!"seccomp_prefill: the translation stopped: {stop.message}"

/-- `n` copies on the trace process's chain, newest at the head, no-new-privs
    set, mode `filter`, `filter_count` `n`. -/
def apply (n : Nat) (sc : SeccompWorld) (t : TaskWorld) : Except String (SeccompWorld × TaskWorld) := do
  if n == 0 || n > PREFILL_MAX then throw s!"seccomp_prefill: {n} copies (1..{PREFILL_MAX})"
  let prog ← translated
  let mut k := sc
  let mut prev : Option FilterId := none
  for _ in [0:n] do
    let id := k.nextFilter
    let flt : SeccompFilter := { id, allowNative, prev, prog := prog.toKernel,
                                 origProg := program.map SockFilter.toKernel }
    k := { k with nextFilter := id + 1, filters := k.filters.insert id flt }
    prev := some id
  let task : Task := { t.task with noNewPrivs := true, seccomp := { mode := .filter, filterCount := n, filter := prev } }
  return (k, { t with task })

end Leanux.Seccomp.Prefill
