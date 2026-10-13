import Leanux.Seccomp.Engine
import Lean.Data.Json

/-!
# The hand-written set for the checker, the translation and the engine

seccomp stream U (docs/2026-10-12-seccomp-design.md, section 8): every
rejection arm of `bpf_check_classic` and `seccomp_check_filter` rejected
at least once, the accepted canonical programs, the `RET|A`, `DIV|X` and
`MOD|X` cases of audit S1, the exact eBPF emission of representative
programs, the allocation and record arms, and the executable equality check
of section 8 (`classicRun` against `MiniInterp` on the translation) over the
built-in programs and their probes. `--corpus <dir>` extends the equality
check to every `filter` list and `seccomp_probe` found in the JSON files
under a directory (stream T's corpus), failing if none is found.

Run: `lake build leanux-seccomp-tests && .lake/build/bin/leanux-seccomp-tests`.
-/

open Leanux.Seccomp
open Leanux.Seccomp.Local (LState LStop)

abbrev Check := Except String Unit

def fail (msg : String) : Check := .error msg
def ok : Check := .ok ()

def ensure (cond : Bool) (msg : String) : Check := if cond then ok else fail msg

/-! ## Programs -/

def LD_W_ABS : UInt16 := BPF_LD ||| BPF_W ||| BPF_ABS
def RET_K : UInt16 := BPF_RET ||| BPF_K
def RET_A : UInt16 := BPF_RET ||| BPF_A
def JEQ_K : UInt16 := BPF_JMP ||| BPF_JEQ ||| BPF_K
def JGT_K : UInt16 := BPF_JMP ||| BPF_JGT ||| BPF_K
def JGE_K : UInt16 := BPF_JMP ||| BPF_JGE ||| BPF_K
def JSET_K : UInt16 := BPF_JMP ||| BPF_JSET ||| BPF_K
def JEQ_X : UInt16 := BPF_JMP ||| BPF_JEQ ||| BPF_X
def JA : UInt16 := BPF_JMP ||| BPF_JA
def errno (e : UInt32) : UInt32 := SECCOMP_RET_ERRNO ||| e
def ALLOW := SECCOMP_RET_ALLOW
def KILL := SECCOMP_RET_KILL_THREAD

/-- `return ALLOW` -/
def allowAll : ClassicProg := #[stmt RET_K ALLOW]

/-- The canonical prologue: the architecture check, then the number. -/
def canonical : ClassicProg := #[
  stmt LD_W_ABS 4, jump JEQ_K AUDIT_ARCH_X86_64 1 0, stmt RET_K KILL,
  stmt LD_W_ABS 0, jump JEQ_K 1 0 1, stmt RET_K ALLOW, stmt RET_K (errno 38)]

/-- allow 1, ERRNO 38 otherwise -/
def nrFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JEQ_K 1 0 1, stmt RET_K ALLOW, stmt RET_K (errno 38)]

/-- `LEN == 64` → ALLOW -/
def lenFilter : ClassicProg := #[
  stmt (BPF_LD ||| BPF_W ||| BPF_LEN) 0, jump JEQ_K 64 0 1, stmt RET_K ALLOW, stmt RET_K KILL]

/-- ALLOW iff args[0] (low word) > 100 -/
def argFilter : ClassicProg := #[
  stmt LD_W_ABS 16, jump JGT_K 100 0 1, stmt RET_K ALLOW, stmt RET_K (errno 1)]

/-- the jump with a negative immediate: nr == 0xffffffff -/
def negImmFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JEQ_K 0xffffffff 0 1, stmt RET_K ALLOW, stmt RET_K KILL]

/-- `jf == 0`: nr > 5 → the second return -/
def jfZeroFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JGT_K 5 1 0, stmt RET_K KILL, stmt RET_K ALLOW]

/-- `jt == 0` on JGE (the JLT conversion, the one-off mutant's target) -/
def jgeFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JGE_K 10 0 1, stmt RET_K ALLOW, stmt RET_K (errno 2)]

/-- `jt == 0` on JSET takes jmp_rest: Jxx then JA -/
def jsetFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JSET_K 1 0 1, stmt RET_K (errno 3), stmt RET_K ALLOW]

/-- both targets non-zero: jmp_rest with two live targets (the first return is dead) -/
def twoTargetsFilter : ClassicProg := #[
  stmt LD_W_ABS 0, jump JEQ_K 7 1 2, stmt RET_K (errno 4), stmt RET_K ALLOW, stmt RET_K KILL]

/-- A = nr; X = A; A = args[0]; A /= X; return A -/
def divXFilter : ClassicProg := #[
  stmt LD_W_ABS 0, stmt (BPF_MISC ||| BPF_TAX) 0, stmt LD_W_ABS 16,
  stmt (BPF_ALU ||| BPF_DIV ||| BPF_X) 0, stmt RET_A 0]

/-- return args[0] (low word) through the accumulator -/
def retAFilter : ClassicProg := #[stmt LD_W_ABS 16, stmt RET_A 0]

/-- a stack cell: store the number, reload it, compare -/
def stackFilter : ClassicProg := #[
  stmt LD_W_ABS 0, stmt BPF_ST 3, stmt (BPF_LD ||| BPF_IMM) 0, stmt (BPF_LD ||| BPF_MEM) 3,
  jump JEQ_K 2 0 1, stmt RET_K ALLOW, stmt RET_K KILL]

/-- shifts by X: a count of 33 masks to 1 -/
def shiftXFilter : ClassicProg := #[
  stmt LD_W_ABS 16, stmt (BPF_MISC ||| BPF_TAX) 0, stmt (BPF_LD ||| BPF_IMM) 1,
  stmt (BPF_ALU ||| BPF_LSH ||| BPF_X) 0, stmt RET_A 0]

/-- JA over a dead return, and an ALU chain with immediates and X -/
def mixedFilter : ClassicProg := #[
  stmt LD_W_ABS 0, stmt JA 1, stmt RET_K KILL,
  stmt (BPF_ALU ||| BPF_ADD ||| BPF_K) 3, stmt (BPF_ALU ||| BPF_MUL ||| BPF_K) 7,
  stmt (BPF_MISC ||| BPF_TAX) 0, stmt LD_W_ABS 24, stmt (BPF_ALU ||| BPF_XOR ||| BPF_X) 0,
  stmt (BPF_ALU ||| BPF_AND ||| BPF_K) 0xff, stmt (BPF_ALU ||| BPF_RSH ||| BPF_K) 1,
  stmt (BPF_ALU ||| BPF_SUB ||| BPF_X) 0, stmt (BPF_ALU ||| BPF_OR ||| BPF_K) 0x70000,
  stmt (BPF_ALU ||| BPF_NEG) 0, stmt (BPF_ALU ||| BPF_NEG) 0,
  jump JEQ_X 0 0 1, stmt RET_K ALLOW, stmt RET_A 0]

def probes : List SeccompData :=
  [{ nr := 1, arch := AUDIT_ARCH_X86_64 }, { nr := 2, arch := AUDIT_ARCH_X86_64 },
   { nr := 0, arch := 0 }, { nr := -1, arch := AUDIT_ARCH_X86_64 },
   { nr := 7, arch := AUDIT_ARCH_X86_64, args := #[0, 0, 0, 0, 0, 0] },
   { nr := 7, arch := AUDIT_ARCH_X86_64, args := #[101, 0, 0, 0, 0, 0] },
   { nr := 2, arch := AUDIT_ARCH_X86_64, args := #[0xffffffffffffffff, 33, 5, 0, 0, 0] },
   { nr := 335, arch := AUDIT_ARCH_X86_64, args := #[33, 1, 2, 3, 4, 5] },
   { nr := 10, arch := AUDIT_ARCH_X86_64, args := #[6, 0x100000000, 0, 0, 0, 0] }]

/-! ## Helpers -/

def install (p : ClassicProg) (st : LState := {}) : Except LStop (Except Int BpfProg × LState) :=
  Local.run (bpfProgCreateFromUser { len := p.size, filter := some p }) st

def installFprog (f : SockFprog) (st : LState := {}) : Except LStop (Except Int BpfProg × LState) :=
  Local.run (bpfProgCreateFromUser f) st

/-- Rejected with `e`, and the last step recorded is `lastLabel`. -/
def rejects (p : ClassicProg) (e : Int) (lastLabel : String) : Check := do
  match install p with
  | .error stop => fail s!"stopped: {stop.message}"
  | .ok (.ok _, _) => fail "accepted"
  | .ok (.error got, st) =>
    if got != e then fail s!"errno {got}, expected {e}" else
    -- the rejecting arm is the last step before the callers' error arms
    let inner := st.labels.filter fun l =>
      !(l.startsWith "bpf_prog_create_from_user." || l.startsWith "bpf_prepare_filter."
        || l.startsWith "__bpf_prog_release." || l.startsWith "bpf_release_orig_filter.")
    match inner.getLast? with
    | some l => ensure (l == lastLabel) s!"last checker step {l}, expected {lastLabel}"
    | none => fail "no checker step recorded"

def accepts (p : ClassicProg) : Except String BpfProg :=
  match install p with
  | .error stop => .error s!"stopped: {stop.message}"
  | .ok (.error e, st) => .error s!"rejected with {e}; last step {st.labels.getLast?.getD "-"}"
  | .ok (.ok prog, _) => .ok prog

def runs (p : ClassicProg) (d : SeccompData) (expected : UInt32) : Check := do
  let prog ← accepts p
  match MiniInterp.run prog d with
  | .error s => fail s!"engine stopped: {repr s}"
  | .ok v => ensure (v == expected) s!"engine returned {v}, expected {expected}"

def agrees (p : ClassicProg) (d : SeccompData) : Check :=
  match checkTranslation p d with
  | .agree _ => ok
  | .rejected e => fail s!"rejected with {e}"
  | .stopped s => fail s!"stopped: {s.message}"
  | .disagree c e => fail s!"classic {repr c}, engine {repr e}"

/-! ## The checks -/

def checkerRejections : List (String × Check) :=
  [("unknown code", rejects #[stmt 0xff 0, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.code_not_allowed=1"),
   ("code over the table", rejects #[stmt 0x1ff 0, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.code_not_allowed=1"),
   ("DIV|K 0", rejects #[stmt (BPF_ALU ||| BPF_DIV ||| BPF_K) 0, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.div_mod_k_zero=1"),
   ("MOD|K 0", rejects #[stmt (BPF_ALU ||| BPF_MOD ||| BPF_K) 0, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.div_mod_k_zero=1"),
   ("LSH|K 32", rejects #[stmt (BPF_ALU ||| BPF_LSH ||| BPF_K) 32, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.shift_k_over_32=1"),
   ("RSH|K 40", rejects #[stmt (BPF_ALU ||| BPF_RSH ||| BPF_K) 40, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.shift_k_over_32=1"),
   ("ST 16", rejects #[stmt BPF_ST 16, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.mem_over_memwords=1"),
   ("LDX|MEM 16", rejects #[stmt (BPF_LDX ||| BPF_MEM) 16, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.mem_over_memwords=1"),
   ("JA past the end", rejects #[stmt JA 1, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.ja_over_end=1"),
   ("jt past the end", rejects #[jump JEQ_K 0 1 0, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.jt_over_end=1"),
   ("jf past the end", rejects #[jump JEQ_K 0 0 1, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.jf_over_end=1"),
   ("last not RET", rejects #[stmt (BPF_LD ||| BPF_IMM) 0] errEINVAL "bpf_check_classic.last_is_ret=0"),
   ("unknown ancillary offset", rejects #[stmt LD_W_ABS 0xfffff001, stmt RET_K ALLOW] errEINVAL "bpf_check_classic.k_over_skf_ad_off=1"),
   ("known ancillary, rejected by seccomp", rejects #[stmt LD_W_ABS 0xfffff000, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.k_over_data_size=1"),
   ("misaligned CTX load", rejects #[stmt LD_W_ABS 2, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.k_misaligned=1"),
   ("CTX load at 64", rejects #[stmt LD_W_ABS 64, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.k_over_data_size=1"),
   ("LD|H|ABS", rejects #[stmt (BPF_LD ||| BPF_H ||| BPF_ABS) 0, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.case_default=1"),
   ("LD|B|IND", rejects #[stmt (BPF_LD ||| BPF_B ||| BPF_IND) 0, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.case_default=1"),
   ("LDX|MSH", rejects #[stmt (BPF_LDX ||| BPF_B ||| BPF_MSH) 0, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.case_default=1"),
   ("MOD|X", rejects #[stmt (BPF_ALU ||| BPF_MOD ||| BPF_X) 0, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.case_default=1"),
   ("MOD|K 1", rejects #[stmt (BPF_ALU ||| BPF_MOD ||| BPF_K) 1, stmt RET_K ALLOW] errEINVAL "seccomp_check_filter.case_default=1"),
   ("load of an unstored cell", rejects #[stmt (BPF_LD ||| BPF_MEM) 0, stmt RET_K ALLOW] errEINVAL "check_load_and_stores.load_unstored=1"),
   ("load of a cell stored on one path",
     rejects #[stmt LD_W_ABS 0, jump JEQ_K 1 0 1, stmt BPF_ST 0, stmt (BPF_LD ||| BPF_MEM) 0, stmt RET_A 0]
       errEINVAL "check_load_and_stores.load_unstored=1"),
   ("NULL filter", match installFprog { len := 1, filter := none } with
     | .ok (.error e, st) => ensure (e == errEINVAL && st.labels.getLast? == some "bpf_prog_create_from_user.basics_not_ok=1") s!"{e} {st.labels}"
     | _ => fail "not rejected"),
   ("len 0", match installFprog { len := 0, filter := some #[] } with
     | .ok (.error e, st) => ensure (e == errEINVAL && st.labels.contains "bpf_check_basics_ok.flen_outside_range=1") s!"{e}"
     | _ => fail "not rejected"),
   ("len 4097", match installFprog { len := 4097, filter := some #[] } with
     | .ok (.error e, st) => ensure (e == errEINVAL && st.labels.contains "bpf_check_basics_ok.flen_outside_range=1") s!"{e}"
     | _ => fail "not rejected"),
   ("a faulting instruction pointer", match installFprog { len := 1, filter := some allowAll, insnsFault := true } with
     | .ok (.error e, st) => ensure (e == errEFAULT && st.labels.getLast? == some "bpf_prog_create_from_user.copy_from_user_fault=1") s!"{e}"
     | _ => fail "not rejected"),
   ("len and instructions disagree", match installFprog { len := 2, filter := some allowAll } with
     | .error (.invariant _) => ok
     | _ => fail "no invariant stop")]

def acceptedPrograms : List (String × ClassicProg) :=
  [("allow-all", allowAll), ("canonical", canonical), ("nr filter", nrFilter), ("LEN filter", lenFilter),
   ("arg filter", argFilter), ("negative immediate", negImmFilter), ("jf == 0", jfZeroFilter),
   ("JGE with jt == 0", jgeFilter), ("JSET with jt == 0", jsetFilter), ("two targets", twoTargetsFilter),
   ("DIV|X", divXFilter), ("RET|A", retAFilter), ("stack cell", stackFilter), ("shift by X", shiftXFilter),
   ("mixed", mixedFilter)]

def acceptance : List (String × Check) :=
  acceptedPrograms.map fun (name, p) => (s!"accepted: {name}", do let _ ← accepts p; ok)

/-- The exact emission for the nr filter: the prologue, the CTX load, the
    JEQ→JNE conversion over the two-instruction return, two returns. -/
def expectedNrFilter : Array BpfInsn := #[
  ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
  ⟨0x61, 0, 6, 0, 0⟩,
  ⟨0x55, 0, 0, 2, 1⟩,
  ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩,
  ⟨0xb4, 0, 0, 0, 0x50026⟩, ⟨0x95, 0, 0, 0, 0⟩]

def expectEmission (p : ClassicProg) (expected : Array BpfInsn) (len stackDepth : Nat) : Check := do
  let prog ← accepts p
  if prog.insns != expected then
    fail s!"emitted {repr prog.insns}, expected {repr expected}"
  ensure (prog.len == len) s!"len {prog.len}, expected {len}" *>
  ensure (prog.stackDepth == stackDepth) s!"stack depth {prog.stackDepth}, expected {stackDepth}" *>
  ensure (prog.origProg == p) "orig_prog is not the original program"

def emission : List (String × Check) :=
  [("nr filter emission", expectEmission nrFilter expectedNrFilter 9 0),
   ("negative immediate: TMP then JNE|X", expectEmission negImmFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩,
      ⟨0xb4, 2, 0, 0, -1⟩, ⟨0x5d, 0, 2, 2, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0⟩, ⟨0x95, 0, 0, 0, 0⟩] 10 0),
   ("jf == 0: JGT as-is", expectEmission jfZeroFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩,
      ⟨0x25, 0, 0, 2, 5⟩,
      ⟨0xb4, 0, 0, 0, 0⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩] 9 0),
   ("jt == 0: JGE becomes JLT", expectEmission jgeFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩,
      ⟨0xa5, 0, 0, 2, 10⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x50002⟩, ⟨0x95, 0, 0, 0, 0⟩] 9 0),
   ("jt == 0 on JSET: Jxx then JA", expectEmission jsetFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩,
      ⟨0x45, 0, 0, 1, 1⟩, ⟨0x05, 0, 0, 2, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x50003⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩] 10 0),
   ("two live targets", expectEmission twoTargetsFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩,
      ⟨0x15, 0, 0, 3, 7⟩, ⟨0x05, 0, 0, 4, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x50004⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0⟩, ⟨0x95, 0, 0, 0, 0⟩] 12 0),
   ("DIV|X: the zero guard", expectEmission divXFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩, ⟨0xbf, 7, 0, 0, 0⟩, ⟨0x61, 0, 6, 16, 0⟩,
      ⟨0xbc, 7, 7, 0, 0⟩, ⟨0x55, 7, 0, 2, 0⟩, ⟨0xac, 0, 0, 0, 0⟩, ⟨0x95, 0, 0, 0, 0⟩, ⟨0x3c, 0, 7, 0, 0⟩,
      ⟨0x95, 0, 0, 0, 0⟩] 12 0),
   ("stack cell: STX/LDX from FP and the depth", expectEmission stackFilter #[
      ⟨0xac, 0, 0, 0, 0⟩, ⟨0xac, 7, 7, 0, 0⟩, ⟨0xbf, 6, 1, 0, 0⟩,
      ⟨0x61, 0, 6, 0, 0⟩, ⟨0x63, 10, 0, -16, 0⟩, ⟨0xb4, 0, 0, 0, 0⟩, ⟨0x61, 0, 10, -16, 0⟩,
      ⟨0x55, 0, 0, 2, 2⟩,
      ⟨0xb4, 0, 0, 0, 0x7fff0000⟩, ⟨0x95, 0, 0, 0, 0⟩,
      ⟨0xb4, 0, 0, 0, 0⟩, ⟨0x95, 0, 0, 0, 0⟩] 12 16),
   ("LEN rewrite: an immediate load of 64", do
      let prog ← accepts lenFilter
      ensure (prog.insns[3]! == ⟨0xb4, 0, 0, 0, 64⟩) s!"{repr prog.insns[3]!}"),
   ("word encoding round trip", do
      for i in expectedNrFilter ++ #[⟨0x63, 10, 7, -64, 0⟩, ⟨0xb4, 2, 0, 0, -1⟩, ⟨0x61, 0, 10, -4, 0x7fffffff⟩] do
        let w := i.toWord
        if BpfInsn.ofWord w != i then throw s!"{repr i} → {w} → {repr (BpfInsn.ofWord w)}"
        if w ≥ 2 ^ 64 then throw s!"{repr i} does not fit a word"
      ensure ((⟨0x63, 10, 7, -16, 0⟩ : BpfInsn).toWord == 0xfff07a63) "the layout of {code, dst|src<<4, off, imm}")]

def engineRuns : List (String × Check) :=
  [("nr filter allows 1", runs nrFilter { nr := 1, arch := AUDIT_ARCH_X86_64 } ALLOW),
   ("nr filter ERRNO 38 on 2", runs nrFilter { nr := 2, arch := AUDIT_ARCH_X86_64 } (errno 38)),
   ("canonical kills a foreign arch", runs canonical { nr := 1, arch := 0 } KILL),
   ("LEN is 64", runs lenFilter { nr := 9, arch := 0 } ALLOW),
   ("arg filter: 101 > 100", runs argFilter { nr := 1, arch := 0, args := #[101, 0, 0, 0, 0, 0] } ALLOW),
   ("arg filter: 100", runs argFilter { nr := 1, arch := 0, args := #[100, 0, 0, 0, 0, 0] } (errno 1)),
   ("arg filter reads the low word", runs argFilter { nr := 1, arch := 0, args := #[0x100000000, 0, 0, 0, 0, 0] } (errno 1)),
   ("negative immediate matches nr -1", runs negImmFilter { nr := -1, arch := 0 } ALLOW),
   ("negative immediate: nr 1", runs negImmFilter { nr := 1, arch := 0 } KILL),
   ("jf == 0: 6 > 5", runs jfZeroFilter { nr := 6, arch := 0 } ALLOW),
   ("jf == 0: 5", runs jfZeroFilter { nr := 5, arch := 0 } KILL),
   ("JGE: 10", runs jgeFilter { nr := 10, arch := 0 } ALLOW),
   ("JGE: 9", runs jgeFilter { nr := 9, arch := 0 } (errno 2)),
   ("JSET: odd", runs jsetFilter { nr := 3, arch := 0 } (errno 3)),
   ("JSET: even", runs jsetFilter { nr := 4, arch := 0 } ALLOW),
   ("two targets: 7 takes jt", runs twoTargetsFilter { nr := 7, arch := 0 } ALLOW),
   ("two targets: 8 takes jf", runs twoTargetsFilter { nr := 8, arch := 0 } KILL),
   ("DIV|X by zero returns 0 (KILL_THREAD)", runs divXFilter { nr := 0, arch := 0, args := #[99, 0, 0, 0, 0, 0] } 0),
   ("DIV|X: 99 / 3", runs divXFilter { nr := 3, arch := 0, args := #[99, 0, 0, 0, 0, 0] } 33),
   ("RET|A: ALLOW from an argument", runs retAFilter { nr := 0, arch := 0, args := #[0x7fff0000, 0, 0, 0, 0, 0] } ALLOW),
   ("RET|A: 0 from an argument", runs retAFilter { nr := 0, arch := 0, args := #[0, 0, 0, 0, 0, 0] } 0),
   ("stack: nr 2 reloaded", runs stackFilter { nr := 2, arch := 0 } ALLOW),
   ("stack: nr 3", runs stackFilter { nr := 3, arch := 0 } KILL),
   ("shift by X: 1 << 33 masks to 2", runs shiftXFilter { nr := 0, arch := 0, args := #[33, 0, 0, 0, 0, 0] } 2),
   ("shift by X: 1 << 31", runs shiftXFilter { nr := 0, arch := 0, args := #[31, 0, 0, 0, 0, 0] } 0x80000000),
   ("ip read is unsupported", do
      let prog ← accepts #[stmt LD_W_ABS 8, stmt RET_A 0]
      match MiniInterp.run prog { nr := 0, arch := 0 } with
      | .error (.unsupportedRead 8) => ok
      | r => fail s!"{repr r}"),
   ("ip read with the ip supplied", do
      let prog ← accepts #[stmt LD_W_ABS 12, stmt RET_A 0]
      match MiniInterp.run prog { nr := 0, arch := 0, ip := some 0x1234567800000001 } with
      | .ok v => ensure (v == 0x12345678) s!"{v}"
      | r => fail s!"{repr r}"),
   ("an opcode outside the contract stops the engine", do
      let prog ← accepts allowAll
      let bad := { prog with insns := prog.insns.set! 3 ⟨0x07, 0, 0, 0, 1⟩ }   -- ALU64 ADD K
      match MiniInterp.run bad { nr := 0, arch := 0 } with
      | .error (.unsupportedInsn 3 0x07) => ok
      | r => fail s!"{repr r}")]

def equality : List (String × Check) :=
  (acceptedPrograms.flatMap fun (name, p) => probes.map fun d => (s!"agree: {name} on nr {d.nr}", agrees p d))
  ++ [("a rejected program is reported as such", match checkTranslation #[stmt 0xff 0, stmt RET_K ALLOW] probes.head! with
        | .rejected e => ensure (e == errEINVAL) s!"{e}"
        | r => fail s!"{repr r}")]

def constAllow : List (String × Check) :=
  [("allow-all is const-allow", ensure (seccompIsConstAllowPure allowAll 59 AUDIT_ARCH_X86_64) ""),
   ("nr filter: 1", ensure (seccompIsConstAllowPure nrFilter 1 AUDIT_ARCH_X86_64) ""),
   ("nr filter: 2", ensure (!seccompIsConstAllowPure nrFilter 2 AUDIT_ARCH_X86_64) ""),
   ("canonical: 1 on the native arch", ensure (seccompIsConstAllowPure canonical 1 AUDIT_ARCH_X86_64) ""),
   ("canonical: 1 on another arch", ensure (!seccompIsConstAllowPure canonical 1 0) ""),
   ("an argument load is not constant", ensure (!seccompIsConstAllowPure argFilter 1 AUDIT_ARCH_X86_64) ""),
   ("the uretprobe exception", ensure (seccompIsConstAllowPure #[stmt RET_K KILL] 335 AUDIT_ARCH_X86_64) ""),
   ("running off the end", ensure (!seccompIsConstAllowPure #[stmt JA 0] 1 0) ""),
   ("const-allow implies ALLOW through the engine", do
      for (name, p) in acceptedPrograms do
        for nr in [0, 1, 2, 3, 7, 59, 335, 1000] do
          if seccompIsConstAllowPure p nr AUDIT_ARCH_X86_64 && nr != 335 then
            for d in probes do
              let d' := { d with nr := nr, arch := AUDIT_ARCH_X86_64 }
              match checkTranslation p d' with
              | .agree (.ok v) => if v != ALLOW then throw s!"{name} on {nr}: const-allow but {v}"
              | r => throw s!"{name} on {nr}: {repr r}")]

/-- Each recorded allocation site, failed once, gives `-ENOMEM` with the
    arm's step last; an unrecorded site in the list changes nothing. -/
def allocationArms : List (String × Check) :=
  [(.kmallocOrigFkprog, "bpf_prog_create_from_user.store_orig_err=1"),
   (.kmemdupOrigFilter, "bpf_prog_create_from_user.store_orig_err=1"),
   (.kmallocArrayMasks, "bpf_prog_create_from_user.prepare_err=1"),
   (.kmemdupArrayOldProg, "bpf_prog_create_from_user.prepare_err=1"),
   (.kcallocAddrs, "bpf_prog_create_from_user.prepare_err=1"),
   (.bpfProgAllocAux, "bpf_prog_create_from_user.prog_alloc_nomem=1")].map (fun (site, last) =>
    (s!"-ENOMEM at {site.info.label}", match install nrFilter { failSites := [site] } with
      | .ok (.error e, st) => ensure (e == errENOMEM && st.labels.getLast? == some last && st.failSites == [])
          s!"errno {e}, last {st.labels.getLast?.getD "-"}"
      | .ok (.ok _, _) => fail "accepted"
      | .error s => fail s.message))
  ++ [("an unrecorded site cannot fail", match install nrFilter { failSites := [.bpfProgAllocImage, .bpfProgReallocImage] } with
        | .ok (.ok _, st) => ensure (st.allocs.all (·.2)) "an unrecorded site answered false"
        | r => fail s!"{repr (r.map (·.1))}"),
      ("the allocation order of one install", match install nrFilter with
        | .ok (.ok _, st) => ensure (st.allocs.map (·.1) == #[.bpfProgAllocImage, .bpfProgAllocAux, .bpfProgAllocActive,
            .bpfProgAllocStats, .kmallocOrigFkprog, .kmemdupOrigFilter, .kmallocArrayMasks, .kmemdupArrayOldProg,
            .bpfProgReallocImage, .kcallocAddrs]) s!"{repr (st.allocs.map (·.1))}"
        | r => fail s!"{repr (r.map (·.1))}")]

def recordArms : List (String × Check) :=
  let words := expectedNrFilter.toList.map (·.toWord)
  [("matching records", match install nrFilter { records := some (words ++ [9]) } with
     | .ok (.ok _, st) => ensure (st.records == some []) "records left over"
     | .ok (.error e, _) => fail s!"rejected {e}"
     | .error s => fail s.message),
   ("a differing instruction", match install nrFilter { records := some ((words.take 4 ++ [(⟨0x15, 0, 0, 2, 1⟩ : BpfInsn).toWord] ++ words.drop 5) ++ [9]) } with
     | .error (.hidden w) => ensure (w.startsWith "translated instruction 4") w
     | r => fail s!"{repr (r.map (·.1))}"),
   ("a differing length", match install nrFilter { records := some (words ++ [10]) } with
     | .error (.hidden w) => ensure (w.startsWith "translated length") w
     | r => fail s!"{repr (r.map (·.1))}"),
   ("too few records", match install nrFilter { records := some (words.take 3) } with
     | .error (.hidden _) => ok
     | r => fail s!"{repr (r.map (·.1))}"),
   ("no records: nothing compared", match install nrFilter { records := none } with
     | .ok (.ok _, _) => ok
     | r => fail s!"{repr (r.map (·.1))}")]

def structure_ : List (String × Check) :=
  [("49 classic codes", ensure (chkCodeAllowedTable.length == 49) s!"{chkCodeAllowedTable.length}"),
   ("38 seccomp codes", ensure (seccompAllowedCodes.length == 38) s!"{seccompAllowedCodes.length}"),
   ("decision labels are unique", do
      let labels := SDecision.all.map (·.info.label)
      ensure (labels.eraseDups.length == labels.length) "a duplicate label"),
   ("every decision enumerates", ensure (SDecision.all.length ≥ 100 && SDecision.all.contains .migSelectRuntimeErr) s!"{SDecision.all.length}"),
   ("the per-instruction decisions are repeatable", ensure
      ([SDecision.checkCodeNotAllowed, .checkCaseJcond, .clsLoadUnstored, .scfCaseAllowed, .convCaseJcond,
        .emitOffAboveMaxRestJa, .convPassChanged].all (·.info.repeatable)
       && !SDecision.createBasicsNotOk.info.repeatable && !SDecision.migOldProgNoMem.info.repeatable) ""),
   ("an accepted install's pass loop runs twice", match install nrFilter with
      | .ok (.ok _, st) =>
        let passes := st.labels.filter (·.startsWith "bpf_convert_filter.pass_changed")
        ensure (passes == ["bpf_convert_filter.pass_changed=1", "bpf_convert_filter.pass_changed=0"]) s!"{passes}"
      | r => fail s!"{repr (r.map (·.1))}"),
   ("the prologue and the only-length arms", match install nrFilter with
      | .ok (.ok _, st) =>
        ensure (st.labels.contains "bpf_convert_filter.prologue=0" && st.labels.contains "bpf_convert_filter.prologue=1"
          && st.labels.contains "bpf_convert_filter.only_length=1" && st.labels.contains "bpf_convert_filter.only_length=0") ""
      | r => fail s!"{repr (r.map (·.1))}")]

/-! ## A corpus directory (stream T): every `filter` list against every probe -/

partial def collect (j : Lean.Json) (filters : Array ClassicProg) (probesFound : Array SeccompData)
    : Array ClassicProg × Array SeccompData :=
  match j with
  | .obj kvs =>
    kvs.toList.foldl (fun (f, p) (k, v) =>
      if k == "filter" then
        match v with
        | .arr rows =>
          let prog? := rows.mapM fun row => match row with
            | .arr #[.num code, .num jt, .num jf, .num k] =>
              if code.exponent == 0 && jt.exponent == 0 && jf.exponent == 0 && k.exponent == 0 then
                some ⟨UInt16.ofNat code.mantissa.toNat, UInt8.ofNat jt.mantissa.toNat, UInt8.ofNat jf.mantissa.toNat, UInt32.ofNat k.mantissa.toNat⟩
              else none
            | _ => none
          match prog? with
          | some prog => (f.push prog, p)
          | none => (f, p)
        | _ => (f, p)
      else if k == "op" && v == .str "seccomp_probe" then
        let nr := match j.getObjVal? "nr" with | .ok (.num n) => n.mantissa | _ => 0
        let args := match j.getObjVal? "args" with
          | .ok (.arr a) => a.map fun x => match x with | .num n => UInt64.ofNat n.mantissa.toNat | _ => 0
          | _ => #[0, 0, 0, 0, 0, 0]
        (f, p.push { nr, arch := AUDIT_ARCH_X86_64, args := if args.size == 6 then args else #[0, 0, 0, 0, 0, 0] })
      else collect v f p) (filters, probesFound)
  | .arr xs => xs.foldl (fun (f, p) x => collect x f p) (filters, probesFound)
  | _ => (filters, probesFound)

partial def jsonFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← jsonFiles e.path)
    else if e.path.extension == some "json" then out := out.push e.path
  return out

def corpusChecks (dir : String) : IO (List (String × Check)) := do
  let mut filters : Array ClassicProg := #[]
  let mut found : Array SeccompData := #[]
  for file in ← jsonFiles dir do
    match Lean.Json.parse (← IO.FS.readFile file) with
    | .error e => return [(s!"corpus {file}", fail s!"invalid JSON: {e}")]
    | .ok j =>
      let (f, p) := collect j #[] #[]
      filters := filters ++ f
      found := found ++ p
  if filters.isEmpty then return [(s!"corpus {dir}", fail "no filter found")]
  let ds := if found.isEmpty then probes.toArray else found
  return (filters.toList.zipIdx.flatMap fun (p, i) => ds.toList.map fun d =>
    (s!"corpus filter {i} ({p.size} insns) on nr {d.nr}", match checkTranslation p d with
      | .agree _ => ok
      | .rejected _ => ok
      | .stopped s => fail s!"stopped: {s.message}"
      | .disagree c e => fail s!"classic {repr c}, engine {repr e}"))

def main (args : List String) : IO UInt32 := do
  let mut checks := checkerRejections ++ acceptance ++ emission ++ engineRuns ++ equality ++ constAllow
    ++ allocationArms ++ recordArms ++ structure_
  match args with
  | ["--corpus", dir] => checks := checks ++ (← corpusChecks dir)
  | [] => pure ()
  | _ =>
    IO.eprintln "usage: leanux-seccomp-tests [--corpus <dir>]"
    return 2
  let mut failures := 0
  for (name, check) in checks do
    match check with
    | .ok () => pure ()
    | .error msg =>
      failures := failures + 1
      IO.println s!"FAIL {name}: {msg}"
  IO.println s!"seccomp tests: {checks.length} checks, {failures} failures"
  return if failures == 0 then 0 else 1
