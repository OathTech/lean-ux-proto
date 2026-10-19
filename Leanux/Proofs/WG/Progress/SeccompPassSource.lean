import Leanux.Seccomp.Bridge

/-! One owned factor of the original converter. Only the outer pass collection
and address-table allocation callback are exposed. The instruction switch stays
in this single factor; the default source equation checks every original path. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompFinite
open Leanux Leanux.Seccomp
def afterAllocationWith {ρ : Type} [ForIn Seccomp.M ρ Unit] (passes : ρ)
    (prog : Seccomp.ClassicProg) (newProg : Option Nat) (seenLdAbsIn : Bool)
    (newLenIn : Nat) (hasAddrs : Bool) (addrsIn : Array Nat) : Seccomp.M (Except Int ConvertOut) := do
  let len := prog.size
  let mut addrs := addrsIn
  let seenLdAbs := seenLdAbsIn
  let mut stackDepth := newProg.getD 0
  let mut newFlen := 0
  let mut pass := 0
  for _ in passes do   -- original do_pass:
    let mut out : Array Seccomp.BpfInsn := #[]
    let mut count := 0   -- new_insn - first_insn
    if ← Seccomp.branch .convPrologue newProg.isSome then
      out := #[alu32Reg BPF_XOR.toUInt8 BPF_REG_A BPF_REG_A, alu32Reg BPF_XOR.toUInt8 BPF_REG_X BPF_REG_X,
               mov64Reg BPF_REG_CTX BPF_REG_ARG1]
      count := 3
      if ← Seccomp.branch .convSeenLdAbs seenLdAbs then
        Seccomp.invariant "bpf_convert_filter: seen_ld_abs prologue; no packet load survives seccomp_check_filter"
    else
      count := 3
    for i in [0:len] do
      let fp := prog[i]!
      let code := fp.code
      let mut tmp : Array Seccomp.BpfInsn := #[]   -- the instructions of tmp_insns before `insn`
      let mut cur : Seccomp.BpfInsn := default      -- `*insn`, zeroed
      if ← Seccomp.branch .convHasAddrs hasAddrs then addrs := addrs.set! i count
      -- the switch (:643), only the taken arm is recorded
      if convAluLoadCodes.contains code then
        let _ ← Seccomp.branch .convCaseAluLoad true
        -- `BPF_CLASS(fp->code) == BPF_LD && BPF_MODE(fp->code) == BPF_ABS && convert_bpf_extensions(fp, &insn)`
        -- one compiled test `(code & 0xe7) == 0x20` (measured), carried by the first decision
        if ← cmpEq .convAluClassLd (code &&& 0xe7).toNat (BPF_LD ||| BPF_ABS).toNat then
          if ← Seccomp.branch .convAluModeAbs true then
            Seccomp.invariant "bpf_convert_filter: convert_bpf_extensions reached; an LD|ABS survived seccomp_check_filter"
        -- `BPF_CLASS(fp->code) == BPF_LD && convert_bpf_ld_abs(fp, &insn)`
        if ← cmpEq .convAluClassLd2 (bpfClass code).toNat BPF_LD.toNat then
          Seccomp.invariant "bpf_convert_filter: convert_bpf_ld_abs reached; an LD|IND survived seccomp_check_filter"
        -- `fp->code == (BPF_ALU | BPF_DIV | BPF_X) || fp->code == (BPF_ALU | BPF_MOD | BPF_X)`
        let divX ← cmpEq .convCodeDivX code.toNat (BPF_ALU ||| BPF_DIV ||| BPF_X).toNat
        let zeroGuard ← if divX then pure true else cmpEq .convCodeModX code.toNat (BPF_ALU ||| BPF_MOD ||| BPF_X).toNat
        if zeroGuard then
          tmp := tmp ++ #[mov32Reg BPF_REG_X BPF_REG_X, jmpImm BPF_JNE BPF_REG_X 0 2,
                          alu32Reg BPF_XOR.toUInt8 BPF_REG_A BPF_REG_A, exitInsn]
        cur := rawInsn code.toUInt8 BPF_REG_A BPF_REG_X 0 (immOf fp.k)
      else if code == (BPF_JMP ||| BPF_JA) then
        let _ ← Seccomp.branch .convCaseJa true
        let target := jaTarget i fp.k
        cur := { cur with code := code.toUInt8 }
        match ← emitJmp .ja target len (if hasAddrs then some addrs else none) i tmp.size with
        | .error e => return .error e
        | .ok off => cur := { cur with off }
      else if jcondCodes.contains code then
        let _ ← Seccomp.branch .convCaseJcond true
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
          let isX ← Seccomp.branch .convJmpSrcX (bsrc == BPF_X.toUInt8)
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
              let _ ← Seccomp.branch .convJtZeroJeq true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JNE ||| bsrc }
            else if op == BPF_JGT.toUInt8 then
              let _ ← Seccomp.branch .convJtZeroJgt true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JLE ||| bsrc }
            else if op == BPF_JGE.toUInt8 then
              let _ ← Seccomp.branch .convJtZeroJge true
              cur := { cur with code := BPF_JMP.toUInt8 ||| BPF_JLT ||| bsrc }
            else
              let _ ← Seccomp.branch .convJtZeroDefault true
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
            cur := { (default : Seccomp.BpfInsn) with code := BPF_JMP.toUInt8 ||| BPF_JA.toUInt8 }
            let target2 : Int := i + fp.jf.toNat + 1
            match ← emitJmp .restJa target2 len (if hasAddrs then some addrs else none) i tmp.size with
            | .error e => return .error e
            | .ok off => cur := { cur with off }
      else if code == (BPF_LDX ||| BPF_MSH ||| BPF_B) then
        let _ ← Seccomp.branch .convCaseLdxMsh true
        Seccomp.invariant "bpf_convert_filter: the LDX|MSH arm; seccomp_check_filter rejects it"
      else if code == (BPF_RET ||| BPF_A) || code == (BPF_RET ||| BPF_K) then
        let _ ← Seccomp.branch .convCaseRet true
        if ← cmpEq .convRetIsK (bpfRval code).toNat BPF_K.toNat then
          tmp := tmp.push (mov32RawK BPF_REG_A (immOf fp.k))
        cur := exitInsn
      else if code == BPF_ST || code == BPF_STX then
        let _ ← Seccomp.branch .convCaseStore true
        let stackOff := fp.k.toNat * 4 + 4
        cur := stxMemW BPF_REG_FP (if bpfClass code == BPF_ST then BPF_REG_A else BPF_REG_X) (-(stackOff : Int))
        -- `new_prog && new_prog->aux->stack_depth < stack_off`
        if ← Seccomp.branch .convStoreHasNewProg newProg.isSome then
          if ← cmpLt .convStackDepthBelow stackDepth stackOff then stackDepth := stackOff
      else if code == (BPF_LD ||| BPF_MEM) || code == (BPF_LDX ||| BPF_MEM) then
        let _ ← Seccomp.branch .convCaseLoadMem true
        let stackOff := fp.k.toNat * 4 + 4
        cur := ldxMemW (if bpfClass code == BPF_LD then BPF_REG_A else BPF_REG_X) BPF_REG_FP (-(stackOff : Int))
      else if code == (BPF_LD ||| BPF_IMM) || code == (BPF_LDX ||| BPF_IMM) then
        let _ ← Seccomp.branch .convCaseImm true
        cur := mov32Imm (if bpfClass code == BPF_LD then BPF_REG_A else BPF_REG_X) (immOf fp.k)
      else if code == (BPF_MISC ||| BPF_TAX) then
        let _ ← Seccomp.branch .convCaseTax true
        cur := mov64Reg BPF_REG_X BPF_REG_A
      else if code == (BPF_MISC ||| BPF_TXA) then
        let _ ← Seccomp.branch .convCaseTxa true
        cur := mov64Reg BPF_REG_A BPF_REG_X
      else if code == (BPF_LD ||| BPF_W ||| BPF_LEN) || code == (BPF_LDX ||| BPF_W ||| BPF_LEN) then
        let _ ← Seccomp.branch .convCaseLen true
        Seccomp.invariant "bpf_convert_filter: the LEN arm; seccomp_check_filter rewrote every LEN load"
      else if code == (BPF_LDX ||| BPF_ABS ||| BPF_W) then
        let _ ← Seccomp.branch .convCaseLdxAbsW true
        cur := ldxMemW BPF_REG_A BPF_REG_CTX (offOf fp.k)
      else
        let _ ← Seccomp.branch .convCaseDefault true
        return .error errEINVAL
      -- insn++; the copy into new_prog
      tmp := tmp.push cur
      if ← Seccomp.branch .convEmitCopy newProg.isSome then out := out ++ tmp
      count := count + tmp.size
    if ← Seccomp.branch .convOnlyLength newProg.isNone then
      let mut newLen := count
      if ← Seccomp.branch .convSeenLdAbsLen seenLdAbs then newLen := newLen + 4
      return .ok { insns := #[], newLen, stackDepth, seenLdAbs }
    pass := pass + 1
    if ← cmpNe .convPassChanged newFlen count then
      newFlen := count
      if ← cmpGt .convPassOverflow pass 2 then return .error errEINVAL
      continue
    -- kfree(addrs); BUG_ON(*new_len != new_flen)
    if newLenIn != newFlen then
      Seccomp.invariant s!"bpf_convert_filter: BUG_ON(*new_len != new_flen): {newLenIn} and {newFlen}"
    return .ok { insns := out, newLen := newLenIn, stackDepth, seenLdAbs }
  Seccomp.invariant "bpf_convert_filter: the pass loop ended without returning"
def withPasses {ρ : Type} [ForIn Seccomp.M ρ Unit] (passes : ρ)
    (allocate : Seccomp.M Bool) (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seenLdAbsIn : Bool) (newLenIn : Nat) : Seccomp.M (Except Int ConvertOut) := do
  let len := prog.size
  -- `len <= 0 || len > BPF_MAXINSNS` is one unsigned compare `(len - 1) > 0xfff` (measured)
  if ← Seccomp.branchCmp .convLenNonpositive (len ≤ 0 || len > BPF_MAXINSNS) (minusOneU len 32) 0xfff then return .error errEINVAL
  if ← Seccomp.branch .convLenOverMax (len > BPF_MAXINSNS) then return .error errEINVAL
  let mut hasAddrs := false
  let mut addrs : Array Nat := #[]
  if ← Seccomp.branch .convHasNewProg newProg.isSome then
    if ← Seccomp.branch .convAddrsNoMem (!(← allocate)) then return .error errENOMEM
    hasAddrs := true
    addrs := Array.replicate len 0
  afterAllocationWith passes prog newProg seenLdAbsIn newLenIn hasAddrs addrs

theorem original_source (prog : Seccomp.ClassicProg) (newProg : Option Nat) (seen : Bool) (newLen : Nat) :
    (bpfConvertFilter prog newProg seen newLen : Seccomp.M _) =
      withPasses Lean.Loop.mk (Seccomp.alloc .kcallocAddrs) prog newProg seen newLen := rfl

end Leanux.Proofs.WG.Progress.SeccompFinite
