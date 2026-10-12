import Leanux.Seccomp.Translate
import Leanux.Seccomp.Local

/-!
# The engine contract, the mirror's instance, and the classic reference semantics

seccomp stream U, design section 4.4 and 4.6 statement 4. The seam is
`kernel/seccomp.c:426`: above it the mirror is anchored control flow; below
it `bpf_prog_run_pin_on_cpu` → `__bpf_prog_run` → the interpreter
`___bpf_prog_run` (kernel/bpf/core.c:1811) is a service with the contract
`BpfEngine`. No decision inside `run` is a mirror decision: `kernel/bpf/
core.c` is not in `correspondence/kcov.json`.

## The terms an instance must satisfy

1. **CTX reads** are `LDX_MEM W` at 4-aligned offsets below 64 (`struct
   seccomp_data`, uapi/linux/seccomp.h:60-66): 0 is `nr` as a 32-bit value,
   4 is `arch`, 8 and 12 the halves of `instruction_pointer` (a stop when
   the data carries none: it is not recorded, design 3.2), `16 + 8k` and
   `20 + 8k` the halves of `args[k]`, little-endian.
2. **The stack** is 16 words at `FP - 4 .. FP - 64`, zero before the run;
   `STX_MEM W` and `LDX_MEM W` from `FP` only.
3. **ALU32 semantics** are the interpreter's (core.c:1841-1889, the `ALU`
   and `SHT` macros): 32-bit wrap; a shift by a register masks the count
   with 31 (the `SHT` macro; the comment at :1841-1852 says a JIT must
   *not* add the mask, so an ISA model of a JIT states its own convention);
   `NEG` is 32-bit negate; `DIV`/`MOD` by a zero register never reach the
   engine (the translation's guard returns 0 before them, filter.c:686-694),
   by a zero immediate never pass the checker (:1091).
4. **Register width.** Every write to `A`, `X` and `TMP` the translation
   emits is 32-bit and zero-extending (`ALU32`, `MOV32_IMM`, `LDX_MEM W`),
   so the 64-bit `BPF_JMP`-class comparisons it emits compare
   zero-extended values; a `K` operand is sign-extended by the interpreter
   (`(u64) IMM`, core.c:2151-2175), which is why the translation moves a
   negative immediate through `TMP` first. `MiniInterp` holds the registers
   as `UInt32` under that invariant; an instance over `UInt64` must
   zero-extend on those writes to meet the same terms. Jumps are
   `off`-relative to the next instruction, 16-bit signed, resolved by the
   translation; `EXIT` returns `R0`; `MOV64_REG` copies.
5. **The result** is the low 32 bits of `R0` (the C's `unsigned int
   (*bpf_func)(ctx, insnsi)`); the engine has no other effect.
6. **Steps.** A translated seccomp program jumps forward only, so a run
   executes at most `len` instructions; `MiniInterp` faults past that.

`MiniInterp` implements exactly the opcodes the translation of a
seccomp-checked program can emit and answers `unsupportedInsn` for anything
else, so a translation defect cannot be absorbed by a permissive engine.
The user's eBPF JIT project would provide a second instance over the same
`BpfProg`; the mirror's `seccompRunFilters` (stream V) is parametric in the
instance.

`classicRun` is the direct semantics of the seccomp-checked classic
language, the left side of statement 4, with the kernel's conventions
(a register shift count masked to 5 bits, `DIV|X` by zero returning 0). It
is the reference for the executable check of design section 8, not the
modelled path.
-/

namespace Leanux.Seccomp

/-- The 64-byte `struct seccomp_data` image the program reads through CTX.
    `ip` is `none` when not recorded (design 3.2); `args` has six entries. -/
structure SeccompData where
  nr : Int
  arch : UInt32
  ip : Option UInt64 := none
  args : Array UInt64 := #[0, 0, 0, 0, 0, 0]
  deriving Repr, BEq, Inhabited

def AUDIT_ARCH_X86_64 : UInt32 := 0xc000003e

inductive EngineStop where
  /-- A CTX read of the `instruction_pointer` words. -/
  | unsupportedRead (offset : Nat)
  /-- An opcode the translation of a seccomp-checked program never emits. -/
  | unsupportedInsn (pc : Nat) (code : UInt8)
  /-- An out-of-range jump, a bad CTX or stack offset, a zero divisor, a
      shift immediate of 32 or more, or running off the end. -/
  | fault (what : String)
  deriving Repr, BEq

instance : BEq (Except EngineStop UInt32) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- A model of the kernel's eBPF interpreter restricted to one entry: run
    `prog` on `ctx` with R1 = CTX, a zeroed 512-byte stack, and return R0's
    low 32 bits. -/
class BpfEngine (E : Type) where
  run : E → BpfProg → SeccompData → Except EngineStop UInt32

/-- `nr` (`int`) as the 32-bit value a `LDX_MEM W` at offset 0 reads. -/
def SeccompData.nrWord (d : SeccompData) : UInt32 :=
  UInt32.ofNat (((d.nr % 4294967296) + 4294967296) % 4294967296).toNat

/-- Term 1: a 32-bit CTX read at `off`. -/
def SeccompData.read (d : SeccompData) (off : Int) : Except EngineStop UInt32 :=
  if d.args.size != 6 then .error (.fault "seccomp_data carries six arguments")
  else if off < 0 || off ≥ 64 || off % 4 != 0 then .error (.fault s!"CTX read at offset {off}")
  else
    let o := off.toNat
    if o == 0 then .ok d.nrWord
    else if o == 4 then .ok d.arch
    else if o < 16 then
      match d.ip with
      | none => .error (.unsupportedRead o)
      | some ip => .ok (if o == 8 then ip.toUInt32 else (ip >>> 32).toUInt32)
    else
      let a := d.args[(o - 16) / 8]!
      .ok (if (o - 16) % 8 == 0 then a.toUInt32 else (a >>> 32).toUInt32)

/-- A `s32` immediate as the 32-bit value an ALU32 operation uses. -/
def immWord (imm : Int) : UInt32 := UInt32.ofNat (((imm % 4294967296) + 4294967296) % 4294967296).toNat

/-- A `s32` immediate sign-extended to `u64`, as a 64-bit compare uses it. -/
def imm64 (imm : Int) : Nat := if imm < 0 then (imm + 18446744073709551616).toNat else imm.toNat

/-- The stack cell of a `FP`-relative offset (term 2), or `none`. -/
def stackCell (off : Int) : Option Nat :=
  if off ≤ -4 && off ≥ -64 && off % 4 == 0 then some ((-off).toNat / 4 - 1) else none

/-! ## The mirror's instance -/

/-- The mirror's engine: the opcodes the translation emits and nothing
    else. -/
inductive MiniInterp where
  | mk

namespace MiniInterp

/-- The registers that hold numbers: `A` (R0), `TMP` (R2), `X` (R7). `ARG1`
    and `CTX` hold the context, `FP` the frame. -/
def numeric (r : UInt8) : Bool := r == BPF_REG_A || r == BPF_REG_TMP || r == BPF_REG_X

def run (prog : BpfProg) (d : SeccompData) : Except EngineStop UInt32 := do
  if d.args.size != 6 then throw (.fault "seccomp_data carries six arguments")
  let insns := prog.insns
  let n := insns.size
  let mut regs : Array UInt32 := Array.replicate 11 0
  let mut stack : Array UInt32 := Array.replicate 16 0
  let mut pc : Nat := 0
  for _ in [0:n] do   -- term 6
    if pc ≥ n then throw (.fault s!"pc {pc} past the end of {n} instructions")
    let i := insns[pc]!
    let code := i.code.toNat
    let cls := code &&& 0x07
    let op := code &&& 0xf0
    let srcK := (code &&& 0x08) == 0
    if cls == BPF_ALU.toNat then
      if i.off != 0 || !numeric i.dst || (!srcK && !numeric i.src) then throw (.unsupportedInsn pc i.code)
      let dst := regs[i.dst.toNat]!
      let srcv : UInt32 := if srcK then immWord i.imm else regs[i.src.toNat]!
      let v : UInt32 ←
        if op == BPF_ADD.toNat then pure (dst + srcv)
        else if op == BPF_SUB.toNat then pure (dst - srcv)
        else if op == BPF_MUL.toNat then pure (dst * srcv)
        else if op == BPF_DIV.toNat then
          if srcv == 0 then throw (.fault s!"division by zero at {pc}") else pure (dst / srcv)
        else if op == BPF_OR.toNat then pure (dst ||| srcv)
        else if op == BPF_AND.toNat then pure (dst &&& srcv)
        else if op == BPF_LSH.toNat then
          if srcK then (if srcv ≥ 32 then throw (.fault s!"shift immediate {srcv} at {pc}") else pure (dst <<< srcv))
          else pure (dst <<< (srcv &&& 31))
        else if op == BPF_RSH.toNat then
          if srcK then (if srcv ≥ 32 then throw (.fault s!"shift immediate {srcv} at {pc}") else pure (dst >>> srcv))
          else pure (dst >>> (srcv &&& 31))
        else if op == BPF_NEG.toNat then pure (0 - dst)
        else if op == BPF_XOR.toNat then pure (dst ^^^ srcv)
        else if op == BPF_MOV.toNat then pure srcv
        else throw (.unsupportedInsn pc i.code)   -- MOD, ARSH, END
      regs := regs.set! i.dst.toNat v
      pc := pc + 1
    else if cls == BPF_ALU64.toNat then
      -- only MOV64_REG: the context binding, or a copy between numeric registers
      if code != (BPF_ALU64 ||| BPF_MOV ||| BPF_X.toUInt8).toNat || i.off != 0 then throw (.unsupportedInsn pc i.code)
      if i.dst == BPF_REG_CTX && i.src == BPF_REG_ARG1 then pc := pc + 1
      else if numeric i.dst && numeric i.src then
        regs := regs.set! i.dst.toNat regs[i.src.toNat]!
        pc := pc + 1
      else throw (.unsupportedInsn pc i.code)
    else if cls == BPF_JMP.toNat then
      if op == BPF_JA.toNat then
        let next : Int := pc + 1 + i.off
        if next < 0 then throw (.fault s!"jump to {next} at {pc}")
        pc := next.toNat
      else if op == BPF_EXIT.toNat then
        return regs[0]!
      else
        if !numeric i.dst || (!srcK && !numeric i.src) then throw (.unsupportedInsn pc i.code)
        let lhs : Nat := regs[i.dst.toNat]!.toNat
        let rhs : Nat := if srcK then imm64 i.imm else regs[i.src.toNat]!.toNat
        let taken ←
          if op == BPF_JEQ.toNat then pure (lhs == rhs)
          else if op == BPF_JNE.toNat then pure (lhs != rhs)
          else if op == BPF_JGT.toNat then pure (lhs > rhs)
          else if op == BPF_JLT.toNat then pure (lhs < rhs)
          else if op == BPF_JGE.toNat then pure (lhs ≥ rhs)
          else if op == BPF_JLE.toNat then pure (lhs ≤ rhs)
          else if op == BPF_JSET.toNat then pure ((lhs &&& rhs) != 0)
          else throw (.unsupportedInsn pc i.code)   -- the signed compares, CALL, JMP32
        if taken then
          let next : Int := pc + 1 + i.off
          if next < 0 then throw (.fault s!"jump to {next} at {pc}")
          pc := next.toNat
        else pc := pc + 1
    else if code == (BPF_LDX ||| BPF_W ||| BPF_MEM).toNat then
      if !numeric i.dst then throw (.unsupportedInsn pc i.code)
      if i.src == BPF_REG_CTX then
        regs := regs.set! i.dst.toNat (← d.read i.off)
      else if i.src == BPF_REG_FP then
        match stackCell i.off with
        | some cell => regs := regs.set! i.dst.toNat stack[cell]!
        | none => throw (.fault s!"stack read at FP{i.off} at {pc}")
      else throw (.unsupportedInsn pc i.code)
      pc := pc + 1
    else if code == (BPF_STX ||| BPF_W ||| BPF_MEM).toNat then
      if i.dst != BPF_REG_FP || !numeric i.src then throw (.unsupportedInsn pc i.code)
      match stackCell i.off with
      | some cell => stack := stack.set! cell regs[i.src.toNat]!
      | none => throw (.fault s!"stack write at FP{i.off} at {pc}")
      pc := pc + 1
    else throw (.unsupportedInsn pc i.code)
  throw (.fault s!"no EXIT within {n} steps")

end MiniInterp

instance : BpfEngine MiniInterp := ⟨fun _ p d => MiniInterp.run p d⟩

/-! ## The classic reference semantics (design 4.6 statement 4) -/

/-- The direct semantics of the seccomp-checked classic language over the
    original or the rewritten program (both load forms, both `LEN` forms),
    with the kernel's conventions: a register shift count masked to 5 bits,
    `DIV|X` by zero returns 0. Not the modelled path. -/
def classicRun (prog : ClassicProg) (d : SeccompData) : Except EngineStop UInt32 := do
  if d.args.size != 6 then throw (.fault "seccomp_data carries six arguments")
  let n := prog.size
  let mut a : UInt32 := 0
  let mut x : UInt32 := 0
  let mut mem : Array UInt32 := Array.replicate 16 0
  let mut pc : Nat := 0
  for _ in [0:n] do
    if pc ≥ n then throw (.fault s!"pc {pc} past the end of {n} instructions")
    let i := prog[pc]!
    let code := i.code
    let k := i.k
    let cell := k.toNat
    let unsupportedC : Except EngineStop Unit := throw (.fault s!"classic code {code} at {pc} is outside the seccomp language")
    if code == (BPF_LD ||| BPF_W ||| BPF_ABS) || code == (BPF_LDX ||| BPF_W ||| BPF_ABS) then
      a ← d.read k.toNat
      pc := pc + 1
    else if code == (BPF_LD ||| BPF_W ||| BPF_LEN) then a := 64; pc := pc + 1
    else if code == (BPF_LDX ||| BPF_W ||| BPF_LEN) then x := 64; pc := pc + 1
    else if code == (BPF_LD ||| BPF_IMM) then a := k; pc := pc + 1
    else if code == (BPF_LDX ||| BPF_IMM) then x := k; pc := pc + 1
    else if code == (BPF_LD ||| BPF_MEM) || code == (BPF_LDX ||| BPF_MEM) || code == BPF_ST || code == BPF_STX then
      if cell ≥ BPF_MEMWORDS then throw (.fault s!"cell {cell} at {pc}")
      if code == (BPF_LD ||| BPF_MEM) then a := mem[cell]!
      else if code == (BPF_LDX ||| BPF_MEM) then x := mem[cell]!
      else if code == BPF_ST then mem := mem.set! cell a
      else mem := mem.set! cell x
      pc := pc + 1
    else if code == (BPF_MISC ||| BPF_TAX) then x := a; pc := pc + 1
    else if code == (BPF_MISC ||| BPF_TXA) then a := x; pc := pc + 1
    else if code == (BPF_RET ||| BPF_K) then return k
    else if code == (BPF_RET ||| BPF_A) then return a
    else if code == (BPF_JMP ||| BPF_JA) then pc := pc + 1 + k.toNat
    else if jcondCodes.contains code then
      let rhs := if bpfSrc code == BPF_X then x else k
      let op := bpfOp code
      let taken := if op == BPF_JEQ then a == rhs else if op == BPF_JGT then a > rhs
        else if op == BPF_JGE then a ≥ rhs else (a &&& rhs) != 0
      pc := pc + 1 + (if taken then i.jt.toNat else i.jf.toNat)
    else if bpfClass code == BPF_ALU then
      let op := bpfOp code
      let byX := bpfSrc code == BPF_X
      let rhs := if byX then x else k
      if op == BPF_ADD then a := a + rhs
      else if op == BPF_SUB then a := a - rhs
      else if op == BPF_MUL then a := a * rhs
      else if op == BPF_DIV then
        if rhs == 0 then
          if byX then return 0 else throw (.fault s!"DIV|K 0 at {pc}: the checker never admits it")
        else a := a / rhs
      else if op == BPF_AND then a := a &&& rhs
      else if op == BPF_OR then a := a ||| rhs
      else if op == BPF_XOR then a := a ^^^ rhs
      else if op == BPF_LSH then
        if byX then a := a <<< (rhs &&& 31)
        else if rhs ≥ 32 then throw (.fault s!"LSH|K {rhs} at {pc}: the checker never admits it")
        else a := a <<< rhs
      else if op == BPF_RSH then
        if byX then a := a >>> (rhs &&& 31)
        else if rhs ≥ 32 then throw (.fault s!"RSH|K {rhs} at {pc}: the checker never admits it")
        else a := a >>> rhs
      else if op == BPF_NEG then a := 0 - a
      else unsupportedC   -- MOD: seccomp_check_filter rejects it
      pc := pc + 1
    else unsupportedC
  throw (.fault s!"no RET within {n} steps")

/-! ## The executable check of design section 8 -/

inductive TranslationCheck where
  /-- The install is rejected with this errno: nothing to compare. -/
  | rejected (errno : Int)
  /-- Both sides agree on this result. -/
  | agree (result : Except EngineStop UInt32)
  | disagree (classic engine : Except EngineStop UInt32)
  /-- The walkers stopped (a mirror invariant, or the domain). -/
  | stopped (stop : Local.LStop)
  deriving Repr

/-- For an accepted program, `classicRun p d` against `MiniInterp.run
    (translate p) d`: the executable shadow of statement 4, run without
    records in the local instance. -/
def checkTranslation (p : ClassicProg) (d : SeccompData) : TranslationCheck :=
  match Local.run (bpfProgCreateFromUser { len := p.size, filter := some p }) with
  | .error stop => .stopped stop
  | .ok (.error e, _) => .rejected e
  | .ok (.ok prog, _) =>
    let c := classicRun p d
    let e := BpfEngine.run MiniInterp.mk prog d
    if c == e then .agree c else .disagree c e

end Leanux.Seccomp
