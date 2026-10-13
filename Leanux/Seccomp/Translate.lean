import Leanux.Seccomp.Classic

/-!
# The classic-to-eBPF translation (net/core/filter.c)

seccomp stream U, design section 4.3. `bpf_prog_create_from_user`
(filter.c:1423-1462) with `bpf_prog_store_orig_filter` (:1150-1170),
`bpf_prepare_filter` (:1329-1366), `bpf_migrate_filter` (:1259-1327) and the
two-pass `bpf_convert_filter` (:576-919) with `BPF_EMIT_JMP` (:706-720).

The emitted program is the C's instruction sequence, instruction for
instruction: the three-instruction prologue, then per classic instruction
the arms of the `switch` (:643-888) in the C's order. The eBPF length is
what `seccomp_attach_filter`'s path budget consumes (design 2.4), and the
kind-309 records (3.3) compare the program instruction by instruction at
the end of the second pass, before `bpf_prog_select_runtime`.

Dead arms, by the rewrite `seccomp_check_filter` made first (design 4.3):
no `LD|ABS`, `LD|IND`, `LDX|MSH` or `LEN` instruction reaches the
conversion, so `convert_bpf_extensions`, `convert_bpf_ld_abs`, the `MSH`
and `LEN` arms and the `seen_ld_abs` prologue are `invariant` stops.

Below the cut (design 2.7, 3.1): `bpf_prog_alloc` (kernel/bpf/core.c:88-160)
is four allocation sites in order, `bpf_prog_realloc` (:245-272) one, and
`bpf_prog_select_runtime` (:2527-2579) selects the interpreter for the
program's stack depth, locks the image and finds no tail call: with
`CONFIG_BPF_JIT` unset it returns no error on these programs. None of
their tests is a mirror decision.
-/

namespace Leanux.Seccomp

/-- `struct bpf_insn` (uapi/linux/bpf.h:72-78): `off` is `s16`, `imm` is
    `s32`; held as `Int` in range. -/
structure BpfInsn where
  code : UInt8
  dst : UInt8
  src : UInt8
  off : Int
  imm : Int
  deriving Repr, BEq, Inhabited

/-- The instruction's eight bytes as the kernel lays them out on x86-64
    (little-endian; `dst_reg` is the low nibble of the second byte): the word
    of a kind-309 record (design 3.3). -/
def BpfInsn.toWord (i : BpfInsn) : Nat :=
  let off16 := ((i.off % 65536) + 65536) % 65536
  let imm32 := ((i.imm % 4294967296) + 4294967296) % 4294967296
  i.code.toNat + (i.dst.toNat + i.src.toNat * 16) * 256 + off16.toNat * 65536 + imm32.toNat * 4294967296

def BpfInsn.ofWord (w : Nat) : BpfInsn :=
  let off16 := w / 65536 % 65536
  let imm32 := w / 4294967296 % 4294967296
  { code := UInt8.ofNat (w % 256), dst := UInt8.ofNat (w / 256 % 16), src := UInt8.ofNat (w / 4096 % 16),
    off := if off16 ≥ 32768 then (off16 : Int) - 65536 else off16,
    imm := if imm32 ≥ 2147483648 then (imm32 : Int) - 4294967296 else imm32 }

/-- `struct bpf_prog` after migration: the eBPF image (`insnsi`), `len`,
    `aux->stack_depth`, and `orig_prog`, the un-rewritten classic program
    `bpf_prog_store_orig_filter` saved, which the cache emulates. -/
structure BpfProg where
  insns : Array BpfInsn
  len : Nat
  stackDepth : Nat
  origProg : ClassicProg
  deriving Repr

/-! ## Registers and opcode parts (include/linux/filter.h:47-63, uapi/linux/bpf.h:17-47) -/

def BPF_REG_A : UInt8 := 0      -- BPF_REG_0
def BPF_REG_ARG1 : UInt8 := 1
def BPF_REG_TMP : UInt8 := 2    -- the scratch register
def BPF_REG_CTX : UInt8 := 6
def BPF_REG_X : UInt8 := 7
def BPF_REG_FP : UInt8 := 10

def BPF_ALU64 : UInt8 := 0x07
def BPF_MOV : UInt8 := 0xb0
def BPF_JNE : UInt8 := 0x50
def BPF_JLT : UInt8 := 0xa0
def BPF_JLE : UInt8 := 0xb0
def BPF_EXIT : UInt8 := 0x90
def S16_MIN : Int := -32768
def S16_MAX : Int := 32767

/-! ## The instruction macros (include/linux/filter.h:114-485) -/

def alu32Reg (op dst src : UInt8) : BpfInsn := ⟨BPF_ALU.toUInt8 ||| op ||| BPF_X.toUInt8, dst, src, 0, 0⟩
def alu32Imm (op dst : UInt8) (imm : Int) : BpfInsn := ⟨BPF_ALU.toUInt8 ||| op ||| BPF_K.toUInt8, dst, 0, 0, imm⟩
def mov64Reg (dst src : UInt8) : BpfInsn := ⟨BPF_ALU64 ||| BPF_MOV ||| BPF_X.toUInt8, dst, src, 0, 0⟩
def mov32Reg (dst src : UInt8) : BpfInsn := ⟨BPF_ALU.toUInt8 ||| BPF_MOV ||| BPF_X.toUInt8, dst, src, 0, 0⟩
def mov32Imm (dst : UInt8) (imm : Int) : BpfInsn := ⟨BPF_ALU.toUInt8 ||| BPF_MOV ||| BPF_K.toUInt8, dst, 0, 0, imm⟩
/-- `BPF_MOV32_RAW(BPF_K, dst, 0, imm)` -/
def mov32RawK (dst : UInt8) (imm : Int) : BpfInsn := mov32Imm dst imm
def jmpImm (op dst : UInt8) (imm off : Int) : BpfInsn := ⟨BPF_JMP.toUInt8 ||| op ||| BPF_K.toUInt8, dst, 0, off, imm⟩
def ldxMemW (dst src : UInt8) (off : Int) : BpfInsn := ⟨BPF_LDX.toUInt8 ||| BPF_W.toUInt8 ||| BPF_MEM.toUInt8, dst, src, off, 0⟩
def stxMemW (dst src : UInt8) (off : Int) : BpfInsn := ⟨BPF_STX.toUInt8 ||| BPF_W.toUInt8 ||| BPF_MEM.toUInt8, dst, src, off, 0⟩
def exitInsn : BpfInsn := ⟨BPF_JMP.toUInt8 ||| BPF_EXIT, 0, 0, 0, 0⟩
def rawInsn (code dst src : UInt8) (off imm : Int) : BpfInsn := ⟨code, dst, src, off, imm⟩

/-- `fp->k` (u32) assigned to a `s32` field. -/
def immOf (k : UInt32) : Int := s32 k
/-- `fp->k` (u32) assigned to the `s16` `off` field. -/
def offOf (k : UInt32) : Int :=
  let low := k.toNat % 65536
  if low ≥ 32768 then (low : Int) - 65536 else low

/-- `target = i + fp->k + 1`: `int + u32` is `u32` arithmetic, assigned to `int`. -/
def jaTarget (i : Nat) (k : UInt32) : Int := s32 (UInt32.ofNat (i + k.toNat + 1))

/-! ## `BPF_EMIT_JMP` (filter.c:706-720) -/

private def emitDecisions : EmitSite → SDecision × SDecision × SDecision × SDecision × SDecision
  | .ja => (.emitTargetOverLenJa, .emitTargetNegativeJa, .emitHasAddrsJa, .emitOffBelowMinJa, .emitOffAboveMaxJa)
  | .jfZero => (.emitTargetOverLenJf, .emitTargetNegativeJf, .emitHasAddrsJf, .emitOffBelowMinJf, .emitOffAboveMaxJf)
  | .jtZero => (.emitTargetOverLenJt, .emitTargetNegativeJt, .emitHasAddrsJt, .emitOffBelowMinJt, .emitOffAboveMaxJt)
  | .rest => (.emitTargetOverLenRest, .emitTargetNegativeRest, .emitHasAddrsRest, .emitOffBelowMinRest, .emitOffAboveMaxRest)
  | .restJa => (.emitTargetOverLenRestJa, .emitTargetNegativeRestJa, .emitHasAddrsRestJa, .emitOffBelowMinRestJa, .emitOffAboveMaxRestJa)

/-- The macro at expansion `site`: the range test on `target`, the offset
    from the `addrs` table (0 in the length-only pass), adjusted for the
    instructions already emitted for this classic one (`insn - tmp_insns`),
    and the `s16` range test. `goto err` is `-EINVAL`. -/
def emitJmp [SeccompM m] (site : EmitSite) (target : Int) (len : Nat) (addrs : Option (Array Nat))
    (i emitted : Nat) : m (Except Int Int) := do
  let (dOver, dNeg, dHas, dMin, dMax) := emitDecisions site
  if ← cmpGe dOver target len then return .error errEINVAL
  -- `target < 0` is recorded at :725 only; elsewhere it is folded into the
  -- unsigned `target >= len` (measured)
  let negative ← match site with
    | .ja => cmpLt dNeg target 0
    | _ => branch dNeg (target < 0)
  if negative then return .error errEINVAL
  let mut off : Int := 0
  if ← branch dHas addrs.isSome then
    let a := addrs.get!
    off := (a[target.toNat]! : Int) - (a[i]! : Int) - 1
  off := off - emitted
  -- `off < S16_MIN || off > S16_MAX` is one compare `(u32)(off + 32768) > 0xffff`
  -- at :725, :778, :785, :790, and folded away at :757 (measured)
  let offU : Int := ((off + 32768) % 4294967296 + 4294967296) % 4294967296
  -- ... and in the length-only pass (no addrs) the compare is folded at every site (measured):
  -- a plain twin decision then
  let outsideOff := off < S16_MIN || off > S16_MAX
  let outside ← match site, addrs with
    | .jfZero, _ => branch dMin outsideOff
    | .ja, none => branch .emitOffRangeJaPass1 outsideOff
    | .jtZero, none => branch .emitOffRangeJtPass1 outsideOff
    | .rest, none => branch .emitOffRangeRestPass1 outsideOff
    | .restJa, none => branch .emitOffRangeRestJaPass1 outsideOff
    | _, some _ => branchCmp dMin outsideOff offU 0xffff
  if outside then return .error errEINVAL
  if ← branch dMax (off > S16_MAX) then return .error errEINVAL
  return .ok off

/-! ## `bpf_convert_filter` (filter.c:576-919) -/

/-- What one call returns through its out-parameters: the emitted program
    (empty for the length-only call), `*new_len`, `new_prog->aux->stack_depth`
    and `*seen_ld_abs`. -/
structure ConvertOut where
  insns : Array BpfInsn
  newLen : Nat
  stackDepth : Nat
  seenLdAbs : Bool
  deriving Repr

/-- The codes of the first `case` group (:645-671): the ALU operations and
    the packet loads that map as-is. -/
def convAluLoadCodes : List UInt16 :=
  [BPF_ALU ||| BPF_ADD ||| BPF_X, BPF_ALU ||| BPF_ADD ||| BPF_K,
   BPF_ALU ||| BPF_SUB ||| BPF_X, BPF_ALU ||| BPF_SUB ||| BPF_K,
   BPF_ALU ||| BPF_AND ||| BPF_X, BPF_ALU ||| BPF_AND ||| BPF_K,
   BPF_ALU ||| BPF_OR ||| BPF_X, BPF_ALU ||| BPF_OR ||| BPF_K,
   BPF_ALU ||| BPF_LSH ||| BPF_X, BPF_ALU ||| BPF_LSH ||| BPF_K,
   BPF_ALU ||| BPF_RSH ||| BPF_X, BPF_ALU ||| BPF_RSH ||| BPF_K,
   BPF_ALU ||| BPF_XOR ||| BPF_X, BPF_ALU ||| BPF_XOR ||| BPF_K,
   BPF_ALU ||| BPF_MUL ||| BPF_X, BPF_ALU ||| BPF_MUL ||| BPF_K,
   BPF_ALU ||| BPF_DIV ||| BPF_X, BPF_ALU ||| BPF_DIV ||| BPF_K,
   BPF_ALU ||| BPF_MOD ||| BPF_X, BPF_ALU ||| BPF_MOD ||| BPF_K,
   BPF_ALU ||| BPF_NEG,
   BPF_LD ||| BPF_ABS ||| BPF_W, BPF_LD ||| BPF_ABS ||| BPF_H, BPF_LD ||| BPF_ABS ||| BPF_B,
   BPF_LD ||| BPF_IND ||| BPF_W, BPF_LD ||| BPF_IND ||| BPF_H, BPF_LD ||| BPF_IND ||| BPF_B]

/-- `bpf_convert_filter(prog, len, new_prog, &new_len, &seen_ld_abs)`.
    `newProg = none` is the length-only call (`new_prog == NULL`);
    `some depth` the emitting call, with `new_prog->aux->stack_depth` at
    `depth` and `*new_len` at `newLenIn` from the first call (the `BUG_ON`
    at :914 compares them). -/
def bpfConvertFilter [SeccompM m] (prog : ClassicProg) (newProg : Option Nat) (seenLdAbsIn : Bool)
    (newLenIn : Nat) : m (Except Int ConvertOut) := do
  let len := prog.size
  -- `len <= 0 || len > BPF_MAXINSNS` is one unsigned compare `(len - 1) > 0xfff` (measured)
  if ← branchCmp .convLenNonpositive (len ≤ 0 || len > BPF_MAXINSNS) (minusOneU len 32) 0xfff then return .error errEINVAL
  if ← branch .convLenOverMax (len > BPF_MAXINSNS) then return .error errEINVAL
  let mut hasAddrs := false
  let mut addrs : Array Nat := #[]
  if ← branch .convHasNewProg newProg.isSome then
    if ← branch .convAddrsNoMem (!(← alloc .kcallocAddrs)) then return .error errENOMEM
    hasAddrs := true
    addrs := Array.replicate len 0
  let seenLdAbs := seenLdAbsIn
  let mut stackDepth := newProg.getD 0
  let mut newFlen := 0
  let mut pass := 0
  repeat   -- do_pass:
    let mut out : Array BpfInsn := #[]
    let mut count := 0   -- new_insn - first_insn
    if ← branch .convPrologue newProg.isSome then
      out := #[alu32Reg BPF_XOR.toUInt8 BPF_REG_A BPF_REG_A, alu32Reg BPF_XOR.toUInt8 BPF_REG_X BPF_REG_X,
               mov64Reg BPF_REG_CTX BPF_REG_ARG1]
      count := 3
      if ← branch .convSeenLdAbs seenLdAbs then
        invariant "bpf_convert_filter: seen_ld_abs prologue; no packet load survives seccomp_check_filter"
    else
      count := 3
    for i in [0:len] do
      let fp := prog[i]!
      let code := fp.code
      let mut tmp : Array BpfInsn := #[]   -- the instructions of tmp_insns before `insn`
      let mut cur : BpfInsn := default      -- `*insn`, zeroed
      if ← branch .convHasAddrs hasAddrs then addrs := addrs.set! i count
      -- the switch (:643), only the taken arm is recorded
      if convAluLoadCodes.contains code then
        let _ ← branch .convCaseAluLoad true
        -- `BPF_CLASS(fp->code) == BPF_LD && BPF_MODE(fp->code) == BPF_ABS && convert_bpf_extensions(fp, &insn)`
        -- one compiled test `(code & 0xe7) == 0x20` (measured), carried by the first decision
        if ← cmpEq .convAluClassLd (code &&& 0xe7).toNat (BPF_LD ||| BPF_ABS).toNat then
          if ← branch .convAluModeAbs true then
            invariant "bpf_convert_filter: convert_bpf_extensions reached; an LD|ABS survived seccomp_check_filter"
        -- `BPF_CLASS(fp->code) == BPF_LD && convert_bpf_ld_abs(fp, &insn)`
        if ← cmpEq .convAluClassLd2 (bpfClass code).toNat BPF_LD.toNat then
          invariant "bpf_convert_filter: convert_bpf_ld_abs reached; an LD|IND survived seccomp_check_filter"
        -- `fp->code == (BPF_ALU | BPF_DIV | BPF_X) || fp->code == (BPF_ALU | BPF_MOD | BPF_X)`
        let divX ← cmpEq .convCodeDivX code.toNat (BPF_ALU ||| BPF_DIV ||| BPF_X).toNat
        let zeroGuard ← if divX then pure true else cmpEq .convCodeModX code.toNat (BPF_ALU ||| BPF_MOD ||| BPF_X).toNat
        if zeroGuard then
          tmp := tmp ++ #[mov32Reg BPF_REG_X BPF_REG_X, jmpImm BPF_JNE BPF_REG_X 0 2,
                          alu32Reg BPF_XOR.toUInt8 BPF_REG_A BPF_REG_A, exitInsn]
        cur := rawInsn code.toUInt8 BPF_REG_A BPF_REG_X 0 (immOf fp.k)
      else if code == (BPF_JMP ||| BPF_JA) then
        let _ ← branch .convCaseJa true
        let target := jaTarget i fp.k
        cur := { cur with code := code.toUInt8 }
        match ← emitJmp .ja target len (if hasAddrs then some addrs else none) i tmp.size with
        | .error e => return .error e
        | .ok off => cur := { cur with off }
      else if jcondCodes.contains code then
        let _ ← branch .convCaseJcond true
        let mut bsrc : UInt8 := 0
        -- `BPF_SRC(fp->code) == BPF_K && (int) fp->k < 0`
        let srcIsK ← cmpEq .convJmpSrcK (bpfSrc code).toNat BPF_K.toNat
        let negative ← if srcIsK then cmpLt .convJmpKNegative (s32 fp.k) 0 else pure false
        if negative then
          tmp := tmp.push (mov32Imm BPF_REG_TMP (immOf fp.k))
          cur := { cur with dst := BPF_REG_A, src := BPF_REG_TMP }
          bsrc := BPF_X.toUInt8
        else
          cur := { cur with dst := BPF_REG_A, imm := immOf fp.k }
          bsrc := (bpfSrc code).toUInt8
          -- plain since stream W's measurement: no comparison record at :750
          let isX ← branch .convJmpSrcX (bsrc == BPF_X.toUInt8)
          cur := { cur with src := if isX then BPF_REG_X else 0 }
        let op := (bpfOp code).toUInt8
        if ← cmpEq .convJfZero fp.jf.toNat 0 then
          cur := { cur with code := BPF_JMP.toUInt8 ||| op ||| bsrc }
          let target : Int := i + fp.jt.toNat + 1
          match ← emitJmp .jfZero target len (if hasAddrs then some addrs else none) i tmp.size with
          | .error e => return .error e
          | .ok off => cur := { cur with off }
        else
          let mut rest := true
          if ← cmpEq .convJtZero fp.jt.toNat 0 then
            rest := false
            if op == BPF_JEQ.toUInt8 then
              let _ ← branch .convJtZeroJeq true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JNE ||| bsrc }
            else if op == BPF_JGT.toUInt8 then
              let _ ← branch .convJtZeroJgt true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JLE ||| bsrc }
            else if op == BPF_JGE.toUInt8 then
              let _ ← branch .convJtZeroJge true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JLT ||| bsrc }
            else
              let _ ← branch .convJtZeroDefault true
              rest := true
            if !rest then
              let target : Int := i + fp.jf.toNat + 1
              match ← emitJmp .jtZero target len (if hasAddrs then some addrs else none) i tmp.size with
              | .error e => return .error e
              | .ok off => cur := { cur with off }
          if rest then   -- jmp_rest: Jxx then JA
            let target : Int := i + fp.jt.toNat + 1
            cur := { cur with code := BPF_JMP.toUInt8 ||| op ||| bsrc }
            match ← emitJmp .rest target len (if hasAddrs then some addrs else none) i tmp.size with
            | .error e => return .error e
            | .ok off => cur := { cur with off }
            tmp := tmp.push cur
            cur := { (default : BpfInsn) with code := BPF_JMP.toUInt8 ||| BPF_JA.toUInt8 }
            let target2 : Int := i + fp.jf.toNat + 1
            match ← emitJmp .restJa target2 len (if hasAddrs then some addrs else none) i tmp.size with
            | .error e => return .error e
            | .ok off => cur := { cur with off }
      else if code == (BPF_LDX ||| BPF_MSH ||| BPF_B) then
        let _ ← branch .convCaseLdxMsh true
        invariant "bpf_convert_filter: the LDX|MSH arm; seccomp_check_filter rejects it"
      else if code == (BPF_RET ||| BPF_A) || code == (BPF_RET ||| BPF_K) then
        let _ ← branch .convCaseRet true
        if ← cmpEq .convRetIsK (bpfRval code).toNat BPF_K.toNat then
          tmp := tmp.push (mov32RawK BPF_REG_A (immOf fp.k))
        cur := exitInsn
      else if code == BPF_ST || code == BPF_STX then
        let _ ← branch .convCaseStore true
        let stackOff := fp.k.toNat * 4 + 4
        cur := stxMemW BPF_REG_FP (if bpfClass code == BPF_ST then BPF_REG_A else BPF_REG_X) (-(stackOff : Int))
        -- `new_prog && new_prog->aux->stack_depth < stack_off`
        if ← branch .convStoreHasNewProg newProg.isSome then
          if ← cmpLt .convStackDepthBelow stackDepth stackOff then stackDepth := stackOff
      else if code == (BPF_LD ||| BPF_MEM) || code == (BPF_LDX ||| BPF_MEM) then
        let _ ← branch .convCaseLoadMem true
        let stackOff := fp.k.toNat * 4 + 4
        cur := ldxMemW (if bpfClass code == BPF_LD then BPF_REG_A else BPF_REG_X) BPF_REG_FP (-(stackOff : Int))
      else if code == (BPF_LD ||| BPF_IMM) || code == (BPF_LDX ||| BPF_IMM) then
        let _ ← branch .convCaseImm true
        cur := mov32Imm (if bpfClass code == BPF_LD then BPF_REG_A else BPF_REG_X) (immOf fp.k)
      else if code == (BPF_MISC ||| BPF_TAX) then
        let _ ← branch .convCaseTax true
        cur := mov64Reg BPF_REG_X BPF_REG_A
      else if code == (BPF_MISC ||| BPF_TXA) then
        let _ ← branch .convCaseTxa true
        cur := mov64Reg BPF_REG_A BPF_REG_X
      else if code == (BPF_LD ||| BPF_W ||| BPF_LEN) || code == (BPF_LDX ||| BPF_W ||| BPF_LEN) then
        let _ ← branch .convCaseLen true
        invariant "bpf_convert_filter: the LEN arm; seccomp_check_filter rewrote every LEN load"
      else if code == (BPF_LDX ||| BPF_ABS ||| BPF_W) then
        let _ ← branch .convCaseLdxAbsW true
        cur := ldxMemW BPF_REG_A BPF_REG_CTX (offOf fp.k)
      else
        let _ ← branch .convCaseDefault true
        return .error errEINVAL
      -- insn++; the copy into new_prog
      tmp := tmp.push cur
      if ← branch .convEmitCopy newProg.isSome then out := out ++ tmp
      count := count + tmp.size
    if ← branch .convOnlyLength newProg.isNone then
      let mut newLen := count
      if ← branch .convSeenLdAbsLen seenLdAbs then newLen := newLen + 4
      return .ok { insns := #[], newLen, stackDepth, seenLdAbs }
    pass := pass + 1
    if ← cmpNe .convPassChanged newFlen count then
      newFlen := count
      if ← cmpGt .convPassOverflow pass 2 then return .error errEINVAL
      continue
    -- kfree(addrs); BUG_ON(*new_len != new_flen)
    if newLenIn != newFlen then
      invariant s!"bpf_convert_filter: BUG_ON(*new_len != new_flen): {newLenIn} and {newFlen}"
    return .ok { insns := out, newLen := newLenIn, stackDepth, seenLdAbs }
  invariant "bpf_convert_filter: the pass loop ended without returning"

/-! ## `bpf_migrate_filter` (filter.c:1259-1327) -/

/-- The kind-309 records (design 3.3): one word per emitted instruction,
    then the length, compared in order against what the mirror emitted. A
    run without records (the domain filter) compares nothing. -/
def checkTranslatedRecords [SeccompM m] (insns : Array BpfInsn) : m Unit := do
  for idx in [0:insns.size] do
    match ← translatedInsn with
    | none => return
    | some w =>
      let mine := insns[idx]!
      if w != mine.toWord then
        recordMismatch s!"translated instruction {idx}: the mirror emits {repr mine}, the kernel recorded {repr (BpfInsn.ofWord w)}"
  match ← translatedLen with
  | none => return
  | some n =>
    if n != insns.size then
      recordMismatch s!"translated length: the mirror emits {insns.size} instructions, the kernel recorded {n}"

/-- `insns` is `fp->insns` after the checks and the rewrite; `orig` the saved
    original. -/
def bpfMigrateFilter [SeccompM m] (insns : ClassicProg) (orig : ClassicProg) : m (Except Int BpfProg) := do
  if ← branch .migOldProgNoMem (!(← alloc .kmemdupArrayOldProg)) then return .error errENOMEM
  -- 1st pass: the new length
  let c1 ← match ← bpfConvertFilter insns none false 0 with
    | .error e =>
      let _ ← branch .migConvert1Err true
      return .error e
    | .ok c =>
      let _ ← branch .migConvert1Err false
      pure c
  -- bpf_prog_realloc (core.c:245-272), below the cut: one page allocation when the image grows
  if ← branch .migReallocNoMem (!(← alloc .bpfProgReallocImage)) then return .error errENOMEM
  -- 2nd pass: the remapping
  let c2 ← match ← bpfConvertFilter insns (some 0) c1.seenLdAbs c1.newLen with
    | .error e =>
      let _ ← branch .migConvert2Err true
      return .error e
    | .ok c =>
      let _ ← branch .migConvert2Err false
      pure c
  -- the kind-309 hook: at the end of the second pass, before the pages are locked
  checkTranslatedRecords c2.insns
  -- bpf_prog_select_runtime (core.c:2527-2579), below the cut: no error on these programs
  if ← branch .migSelectRuntimeErr false then
    invariant "bpf_migrate_filter: bpf_prog_select_runtime failed; the cut assumes it cannot"
  return .ok { insns := c2.insns, len := c2.newLen, stackDepth := c2.stackDepth, origProg := orig }

/-! ## `bpf_prepare_filter` (filter.c:1329-1366), with `trans = seccomp_check_filter` -/

def bpfPrepareFilter [SeccompM m] (insns : ClassicProg) (orig : ClassicProg) : m (Except Int BpfProg) := do
  -- fp->bpf_func = NULL; fp->jited = 0;
  match ← bpfCheckClassic insns with
  | .error e =>
    let _ ← branch .prepCheckClassicErr true
    -- __bpf_prog_release(fp): the type is BPF_PROG_TYPE_UNSPEC, orig_prog is saved
    let _ ← branch .releaseSocketFilter false
    let _ ← branch .releaseOrigHasFprog true
    return .error e
  | .ok () =>
    let _ ← branch .prepCheckClassicErr false
  let mut fp := insns
  if ← branch .prepHasTrans true then
    match ← seccompCheckFilter fp with
    | .error e =>
      let _ ← branch .prepTransErr true
      let _ ← branch .releaseSocketFilter false
      let _ ← branch .releaseOrigHasFprog true
      return .error e
    | .ok rewritten =>
      let _ ← branch .prepTransErr false
      fp := rewritten
  -- bpf_jit_compile: the weak no-op; jited stays 0
  if ← branch .prepNotJited true then bpfMigrateFilter fp orig
  else invariant "bpf_prepare_filter: a jited classic filter; there is no classic JIT on x86-64"

/-! ## `bpf_prog_store_orig_filter` (filter.c:1150-1170) -/

def bpfProgStoreOrigFilter [SeccompM m] : m (Except Int Unit) := do
  if ← branch .storeOrigNoMem (!(← alloc .kmallocOrigFkprog)) then return .error errENOMEM
  if ← branch .storeOrigFilterNoMem (!(← alloc .kmemdupOrigFilter)) then return .error errENOMEM
  return .ok ()

/-! ## `bpf_prog_create_from_user` (filter.c:1423-1462), `trans = seccomp_check_filter`, `save_orig = true` -/

/-- `bpf_prog_alloc` (core.c:142-160) through `bpf_prog_alloc_no_stats`
    (:88-131), below the cut: the image, the aux, the active counter and
    the stats, each freeing the earlier ones on failure. -/
def bpfProgAlloc [SeccompM m] : m Bool := do
  if !(← alloc .bpfProgAllocImage) then return false
  if !(← alloc .bpfProgAllocAux) then return false
  if !(← alloc .bpfProgAllocActive) then return false
  alloc .bpfProgAllocStats

def bpfProgCreateFromUser [SeccompM m] (fprog : SockFprog) : m (Except Int BpfProg) := do
  if ← branch .createBasicsNotOk (!(← bpfCheckBasicsOk fprog.filter fprog.len)) then return .error errEINVAL
  if ← branch .createProgAllocNoMem (!(← bpfProgAlloc)) then return .error errENOMEM
  if ← branch .createCopyFault fprog.insnsFault then return .error errEFAULT
  let insns := fprog.filter.get!
  if insns.size != fprog.len then
    invariant s!"bpf_prog_create_from_user: {insns.size} instructions supplied for len {fprog.len}"
  if ← branch .createSaveOrig true then
    match ← bpfProgStoreOrigFilter with
    | .error _ =>
      let _ ← branch .createStoreOrigErr true
      return .error errENOMEM
    | .ok () =>
      let _ ← branch .createStoreOrigErr false
  match ← bpfPrepareFilter insns insns with
  | .error e =>
    let _ ← branch .createPrepareErr true
    return .error e
  | .ok p =>
    let _ ← branch .createPrepareErr false
    return .ok p

end Leanux.Seccomp
