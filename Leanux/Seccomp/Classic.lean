import Leanux.Seccomp.Decisions

/-!
# Classic BPF programs and their checking (net/core/filter.c, kernel/seccomp.c)

seccomp stream U, design section 4.2. `bpf_check_classic` (filter.c:1072-1148)
with `chk_code_allowed` (:981-1045) and `check_load_and_stores` (:928-979);
`bpf_check_basics_ok` (:1047-1056); `seccomp_check_filter` (seccomp.c:280-347),
which rewrites the program in place. Each walks the program in the C's order
and records the C's decisions; the per-instruction ones are repeatable.

Also here, decision-free: `seccompIsConstAllowPure`, a direct reading of
`seccomp_is_const_allow` (seccomp.c:762-836) over the un-rewritten program
for the executable shadow of design 4.6 statement 2. The modelled path's
version, with its decisions, is stream V's (`Filter.lean`).

Configured-program notes: `bpf_jit_compile` is the weak no-op (no classic
JIT on x86-64, `CONFIG_BPF_JIT` unset), so every filter is migrated to eBPF
(`Translate.lean`). There is no compat architecture (`SECCOMP_ARCH_COMPAT`
undefined), so `seccomp_uprobe_exception` tests only the call number.
-/

namespace Leanux.Seccomp

/-- `struct sock_filter` (uapi/linux/filter.h:24-29). -/
structure SockFilter where
  code : UInt16
  jt : UInt8
  jf : UInt8
  k : UInt32
  deriving Repr, BEq, Inhabited

abbrev ClassicProg := Array SockFilter

/-- `BPF_STMT(code, k)` -/
def stmt (code : UInt16) (k : UInt32) : SockFilter := ⟨code, 0, 0, k⟩
/-- `BPF_JUMP(code, k, jt, jf)` -/
def jump (code : UInt16) (k : UInt32) (jt jf : UInt8) : SockFilter := ⟨code, jt, jf, k⟩

/-! ## The instruction encoding (uapi/linux/bpf_common.h, uapi/linux/filter.h) -/

def BPF_LD : UInt16 := 0x00
def BPF_LDX : UInt16 := 0x01
def BPF_ST : UInt16 := 0x02
def BPF_STX : UInt16 := 0x03
def BPF_ALU : UInt16 := 0x04
def BPF_JMP : UInt16 := 0x05
def BPF_RET : UInt16 := 0x06
def BPF_MISC : UInt16 := 0x07
def BPF_W : UInt16 := 0x00
def BPF_H : UInt16 := 0x08
def BPF_B : UInt16 := 0x10
def BPF_IMM : UInt16 := 0x00
def BPF_ABS : UInt16 := 0x20
def BPF_IND : UInt16 := 0x40
def BPF_MEM : UInt16 := 0x60
def BPF_LEN : UInt16 := 0x80
def BPF_MSH : UInt16 := 0xa0
def BPF_ADD : UInt16 := 0x00
def BPF_SUB : UInt16 := 0x10
def BPF_MUL : UInt16 := 0x20
def BPF_DIV : UInt16 := 0x30
def BPF_OR : UInt16 := 0x40
def BPF_AND : UInt16 := 0x50
def BPF_LSH : UInt16 := 0x60
def BPF_RSH : UInt16 := 0x70
def BPF_NEG : UInt16 := 0x80
def BPF_MOD : UInt16 := 0x90
def BPF_XOR : UInt16 := 0xa0
def BPF_JA : UInt16 := 0x00
def BPF_JEQ : UInt16 := 0x10
def BPF_JGT : UInt16 := 0x20
def BPF_JGE : UInt16 := 0x30
def BPF_JSET : UInt16 := 0x40
def BPF_K : UInt16 := 0x00
def BPF_X : UInt16 := 0x08
def BPF_A : UInt16 := 0x10
def BPF_TAX : UInt16 := 0x00
def BPF_TXA : UInt16 := 0x80

def bpfClass (c : UInt16) : UInt16 := c &&& 0x07
def bpfSize (c : UInt16) : UInt16 := c &&& 0x18
def bpfMode (c : UInt16) : UInt16 := c &&& 0xe0
def bpfOp (c : UInt16) : UInt16 := c &&& 0xf0
def bpfSrc (c : UInt16) : UInt16 := c &&& 0x08
def bpfRval (c : UInt16) : UInt16 := c &&& 0x18

def BPF_MEMWORDS : Nat := 16
def BPF_MAXINSNS : Nat := 4096
/-- `SKF_AD_OFF` (-0x1000) as the `u32` the checker compares `k` with. -/
def SKF_AD_OFF : UInt32 := 0xfffff000
/-- `sizeof(struct seccomp_data)` -/
def SECCOMP_DATA_SIZE : Nat := 64

/-! ## The actions (uapi/linux/seccomp.h:38-51) -/

def SECCOMP_RET_KILL_PROCESS : UInt32 := 0x80000000
def SECCOMP_RET_KILL_THREAD : UInt32 := 0x00000000
def SECCOMP_RET_TRAP : UInt32 := 0x00030000
def SECCOMP_RET_ERRNO : UInt32 := 0x00050000
def SECCOMP_RET_USER_NOTIF : UInt32 := 0x7fc00000
def SECCOMP_RET_TRACE : UInt32 := 0x7ff00000
def SECCOMP_RET_LOG : UInt32 := 0x7ffc0000
def SECCOMP_RET_ALLOW : UInt32 := 0x7fff0000
def SECCOMP_RET_ACTION_FULL : UInt32 := 0xffff0000
def SECCOMP_RET_ACTION : UInt32 := 0x7fff0000
def SECCOMP_RET_DATA : UInt32 := 0x0000ffff
/-- `__NR_uretprobe` on x86-64 (arch/x86/entry/syscalls/syscall_64.tbl). -/
def NR_URETPROBE : Int := 335

/-! ## `chk_code_allowed` (filter.c:981-1045) -/

/-- The 49 true entries of `codes[]` (:982-1037). -/
def chkCodeAllowedTable : List UInt16 :=
  [BPF_ALU ||| BPF_ADD ||| BPF_K, BPF_ALU ||| BPF_ADD ||| BPF_X,
   BPF_ALU ||| BPF_SUB ||| BPF_K, BPF_ALU ||| BPF_SUB ||| BPF_X,
   BPF_ALU ||| BPF_MUL ||| BPF_K, BPF_ALU ||| BPF_MUL ||| BPF_X,
   BPF_ALU ||| BPF_DIV ||| BPF_K, BPF_ALU ||| BPF_DIV ||| BPF_X,
   BPF_ALU ||| BPF_MOD ||| BPF_K, BPF_ALU ||| BPF_MOD ||| BPF_X,
   BPF_ALU ||| BPF_AND ||| BPF_K, BPF_ALU ||| BPF_AND ||| BPF_X,
   BPF_ALU ||| BPF_OR ||| BPF_K, BPF_ALU ||| BPF_OR ||| BPF_X,
   BPF_ALU ||| BPF_XOR ||| BPF_K, BPF_ALU ||| BPF_XOR ||| BPF_X,
   BPF_ALU ||| BPF_LSH ||| BPF_K, BPF_ALU ||| BPF_LSH ||| BPF_X,
   BPF_ALU ||| BPF_RSH ||| BPF_K, BPF_ALU ||| BPF_RSH ||| BPF_X,
   BPF_ALU ||| BPF_NEG,
   BPF_LD ||| BPF_W ||| BPF_ABS, BPF_LD ||| BPF_H ||| BPF_ABS, BPF_LD ||| BPF_B ||| BPF_ABS,
   BPF_LD ||| BPF_W ||| BPF_LEN,
   BPF_LD ||| BPF_W ||| BPF_IND, BPF_LD ||| BPF_H ||| BPF_IND, BPF_LD ||| BPF_B ||| BPF_IND,
   BPF_LD ||| BPF_IMM, BPF_LD ||| BPF_MEM,
   BPF_LDX ||| BPF_W ||| BPF_LEN, BPF_LDX ||| BPF_B ||| BPF_MSH, BPF_LDX ||| BPF_IMM, BPF_LDX ||| BPF_MEM,
   BPF_ST, BPF_STX,
   BPF_MISC ||| BPF_TAX, BPF_MISC ||| BPF_TXA,
   BPF_RET ||| BPF_K, BPF_RET ||| BPF_A,
   BPF_JMP ||| BPF_JA,
   BPF_JMP ||| BPF_JEQ ||| BPF_K, BPF_JMP ||| BPF_JEQ ||| BPF_X,
   BPF_JMP ||| BPF_JGE ||| BPF_K, BPF_JMP ||| BPF_JGE ||| BPF_X,
   BPF_JMP ||| BPF_JGT ||| BPF_K, BPF_JMP ||| BPF_JGT ||| BPF_X,
   BPF_JMP ||| BPF_JSET ||| BPF_K, BPF_JMP ||| BPF_JSET ||| BPF_X]

/-- `ARRAY_SIZE(codes)`: the designated initialiser's largest index is
    `BPF_LDX | BPF_B | BPF_MSH` = 0xb1, so the array has 0xb2 entries. -/
def CHK_CODES_SIZE : Nat := 0xb2

def chkCodeAllowed [SeccompM m] (code : UInt16) : m Bool := do
  if ← cmpGe .chkCodeOverTable code.toNat CHK_CODES_SIZE then return false
  return chkCodeAllowedTable.contains code

/-- The ancillary offsets `SKF_AD_*` (uapi/linux/filter.h:66-81) that
    `bpf_anc_helper` (include/linux/filter.h:1458-1491) recognises on an
    `LD|{W,H,B}|ABS`, as `k - SKF_AD_OFF`. -/
def skfAdOffsets : List UInt32 := [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]

/-- `bpf_anc_helper(ftest) & BPF_ANC`: whether the load is an ancillary one.
    Returns the helper's value (`BPF_ANC | SKF_AD_x`, or 0), so the flag
    test can report the C's operands. -/
def bpfAncHelper (f : SockFilter) : Nat :=
  let isLdAbs := f.code == (BPF_LD ||| BPF_W ||| BPF_ABS) || f.code == (BPF_LD ||| BPF_H ||| BPF_ABS)
    || f.code == (BPF_LD ||| BPF_B ||| BPF_ABS)
  if isLdAbs && f.k ≥ SKF_AD_OFF && skfAdOffsets.contains (f.k - SKF_AD_OFF) then
    0x8000 + (f.k - SKF_AD_OFF).toNat
  else 0

/-! ## `check_load_and_stores` (filter.c:928-979) -/

/-- The eight conditional-jump codes. -/
def jcondCodes : List UInt16 :=
  [BPF_JMP ||| BPF_JEQ ||| BPF_K, BPF_JMP ||| BPF_JEQ ||| BPF_X,
   BPF_JMP ||| BPF_JGE ||| BPF_K, BPF_JMP ||| BPF_JGE ||| BPF_X,
   BPF_JMP ||| BPF_JGT ||| BPF_K, BPF_JMP ||| BPF_JGT ||| BPF_X,
   BPF_JMP ||| BPF_JSET ||| BPF_K, BPF_JMP ||| BPF_JSET ||| BPF_X]

/-- A forward dataflow over the 16 cells: the valid set at an instruction is
    the intersection over its incoming edges (`masks[target] &= memvalid`),
    and a load of a cell not stored on every path is `-EINVAL`. `masks` is
    the `kmalloc_array` (site 8) with its `-ENOMEM` arm. -/
def checkLoadAndStores [SeccompM m] (filter : ClassicProg) : m (Except Int Unit) := do
  let flen := filter.size
  if ← branch .clsMasksNoMem (!(← alloc .kmallocArrayMasks)) then return .error errENOMEM
  let mut masks : Array UInt16 := Array.replicate flen 0xffff
  let mut memvalid : UInt16 := 0
  for pc in [0:flen] do
    memvalid := memvalid &&& masks[pc]!
    let f := filter[pc]!
    let bit : UInt16 := 1 <<< f.k.toUInt16   -- k < BPF_MEMWORDS after bpf_check_classic's test
    if f.code == BPF_ST || f.code == BPF_STX then
      let _ ← branch .clsCaseStore true
      memvalid := memvalid ||| bit
    else if f.code == (BPF_LD ||| BPF_MEM) || f.code == (BPF_LDX ||| BPF_MEM) then
      let _ ← branch .clsCaseLoad true
      if ← branchCmp .clsLoadUnstored ((memvalid &&& bit) == 0) memvalid.toNat bit.toNat then
        return .error errEINVAL
    else if f.code == (BPF_JMP ||| BPF_JA) then
      let _ ← branch .clsCaseJa true
      let target := pc + 1 + f.k.toNat
      if target ≥ flen then invariant "check_load_and_stores: a JA target past the end survived bpf_check_classic"
      masks := masks.set! target (masks[target]! &&& memvalid)
      memvalid := 0xffff
    else if jcondCodes.contains f.code then
      let _ ← branch .clsCaseJcond true
      let t1 := pc + 1 + f.jt.toNat
      let t2 := pc + 1 + f.jf.toNat
      if t1 ≥ flen || t2 ≥ flen then invariant "check_load_and_stores: a conditional target past the end survived bpf_check_classic"
      masks := masks.set! t1 (masks[t1]! &&& memvalid)
      masks := masks.set! t2 (masks[t2]! &&& memvalid)
      memvalid := 0xffff
  return .ok ()

/-! ## `bpf_check_classic` (filter.c:1072-1148) -/

def bpfCheckClassic [SeccompM m] (filter : ClassicProg) : m (Except Int Unit) := do
  let flen := filter.size
  if flen == 0 then invariant "bpf_check_classic on an empty program (bpf_check_basics_ok admits none)"
  for pc in [0:flen] do
    let ftest := filter[pc]!
    let code := ftest.code
    if ← branch .checkCodeNotAllowed (!(← chkCodeAllowed code)) then return .error errEINVAL
    -- the switch (:1087), only the taken arm is recorded
    if code == (BPF_ALU ||| BPF_DIV ||| BPF_K) || code == (BPF_ALU ||| BPF_MOD ||| BPF_K) then
      let _ ← branch .checkCaseDivModK true
      if ← cmpEq .checkDivModKZero (u32 ftest.k) 0 then return .error errEINVAL
    else if code == (BPF_ALU ||| BPF_LSH ||| BPF_K) || code == (BPF_ALU ||| BPF_RSH ||| BPF_K) then
      let _ ← branch .checkCaseShiftK true
      if ← cmpGe .checkShiftKRange (u32 ftest.k) 32 then return .error errEINVAL
    else if code == (BPF_LD ||| BPF_MEM) || code == (BPF_LDX ||| BPF_MEM) || code == BPF_ST || code == BPF_STX then
      let _ ← branch .checkCaseMem true
      if ← cmpGe .checkMemIndex (u32 ftest.k) BPF_MEMWORDS then return .error errEINVAL
    else if code == (BPF_JMP ||| BPF_JA) then
      let _ ← branch .checkCaseJa true
      -- `(unsigned int)(flen - pc - 1)`: non-negative since pc < flen
      if ← cmpGe .checkJaRange (u32 ftest.k) (flen - pc - 1) then return .error errEINVAL
    else if jcondCodes.contains code then
      let _ ← branch .checkCaseJcond true
      if ← cmpGe .checkJtRange (pc + ftest.jt.toNat + 1) flen then return .error errEINVAL
      if ← cmpGe .checkJfRange (pc + ftest.jf.toNat + 1) flen then return .error errEINVAL
    else if code == (BPF_LD ||| BPF_W ||| BPF_ABS) || code == (BPF_LD ||| BPF_H ||| BPF_ABS)
        || code == (BPF_LD ||| BPF_B ||| BPF_ABS) then
      let _ ← branch .checkCaseLdAbs true
      let helper := bpfAncHelper ftest
      let ancFound ← branchCmp .checkAncFound ((helper &&& 0x8000) != 0) helper 0x8000
      if ← cmpEq .checkAncNotFound (if ancFound then 1 else 0) 0 then
        if ← cmpGe .checkAncOffset (u32 ftest.k) (u32 SKF_AD_OFF) then return .error errEINVAL
  let last := filter[flen - 1]!
  if ← branch .checkLastRet (last.code == (BPF_RET ||| BPF_K) || last.code == (BPF_RET ||| BPF_A)) then
    checkLoadAndStores filter
  else return .error errEINVAL

/-! ## `bpf_check_basics_ok` (filter.c:1047-1056), inlined into `bpf_prog_create_from_user` -/

/-- `filter` is the user pointer (`none`: NULL), `flen` the length given. -/
def bpfCheckBasicsOk [SeccompM m] (filter : Option ClassicProg) (flen : Nat) : m Bool := do
  if ← branch .basicsFilterNull filter.isNone then return false
  if ← cmpEq .basicsLenZero flen 0 then return false
  if ← cmpGt .basicsLenOverMax flen BPF_MAXINSNS then return false
  return true

/-! ## `seccomp_check_filter` (seccomp.c:280-347) -/

/-- The 38 codes the second `case` group passes unchanged (:304-342). `MOD`
    is not among them. -/
def seccompAllowedCodes : List UInt16 :=
  [BPF_RET ||| BPF_K, BPF_RET ||| BPF_A,
   BPF_ALU ||| BPF_ADD ||| BPF_K, BPF_ALU ||| BPF_ADD ||| BPF_X,
   BPF_ALU ||| BPF_SUB ||| BPF_K, BPF_ALU ||| BPF_SUB ||| BPF_X,
   BPF_ALU ||| BPF_MUL ||| BPF_K, BPF_ALU ||| BPF_MUL ||| BPF_X,
   BPF_ALU ||| BPF_DIV ||| BPF_K, BPF_ALU ||| BPF_DIV ||| BPF_X,
   BPF_ALU ||| BPF_AND ||| BPF_K, BPF_ALU ||| BPF_AND ||| BPF_X,
   BPF_ALU ||| BPF_OR ||| BPF_K, BPF_ALU ||| BPF_OR ||| BPF_X,
   BPF_ALU ||| BPF_XOR ||| BPF_K, BPF_ALU ||| BPF_XOR ||| BPF_X,
   BPF_ALU ||| BPF_LSH ||| BPF_K, BPF_ALU ||| BPF_LSH ||| BPF_X,
   BPF_ALU ||| BPF_RSH ||| BPF_K, BPF_ALU ||| BPF_RSH ||| BPF_X,
   BPF_ALU ||| BPF_NEG,
   BPF_LD ||| BPF_IMM, BPF_LDX ||| BPF_IMM,
   BPF_MISC ||| BPF_TAX, BPF_MISC ||| BPF_TXA,
   BPF_LD ||| BPF_MEM, BPF_LDX ||| BPF_MEM,
   BPF_ST, BPF_STX,
   BPF_JMP ||| BPF_JA,
   BPF_JMP ||| BPF_JEQ ||| BPF_K, BPF_JMP ||| BPF_JEQ ||| BPF_X,
   BPF_JMP ||| BPF_JGE ||| BPF_K, BPF_JMP ||| BPF_JGE ||| BPF_X,
   BPF_JMP ||| BPF_JGT ||| BPF_K, BPF_JMP ||| BPF_JGT ||| BPF_X,
   BPF_JMP ||| BPF_JSET ||| BPF_K, BPF_JMP ||| BPF_JSET ||| BPF_X]

/-- Walks the checked program, rewriting in place: `LD|W|ABS` becomes
    `LDX|W|ABS` and must be an aligned offset below 64; the two `LEN` loads
    become immediate loads of 64; the 38 codes pass; the rest is `-EINVAL`.
    Returns the rewritten program (`fp->insns`); the original was already
    saved by `bpf_prog_store_orig_filter`. -/
def seccompCheckFilter [SeccompM m] (filter : ClassicProg) : m (Except Int ClassicProg) := do
  let mut out := filter
  for pc in [0:filter.size] do
    let ftest := out[pc]!
    let code := ftest.code
    let k := ftest.k
    if code == (BPF_LD ||| BPF_W ||| BPF_ABS) then
      let _ ← branch .scfCaseLdAbsW true
      out := out.set! pc { ftest with code := BPF_LDX ||| BPF_W ||| BPF_ABS }
      if ← cmpGe .scfCtxOffsetRange (u32 k) SECCOMP_DATA_SIZE then return .error errEINVAL
      if ← branchCmp .scfCtxMisaligned ((k &&& 3) != 0) (u32 k) 3 then return .error errEINVAL
    else if code == (BPF_LD ||| BPF_W ||| BPF_LEN) then
      let _ ← branch .scfCaseLdLen true
      out := out.set! pc { ftest with code := BPF_LD ||| BPF_IMM, k := SECCOMP_DATA_SIZE.toUInt32 }
    else if code == (BPF_LDX ||| BPF_W ||| BPF_LEN) then
      let _ ← branch .scfCaseLdxLen true
      out := out.set! pc { ftest with code := BPF_LDX ||| BPF_IMM, k := SECCOMP_DATA_SIZE.toUInt32 }
    else if seccompAllowedCodes.contains code then
      let _ ← branch .scfCaseAllowed true
    else
      let _ ← branch .scfCaseDefault true
      return .error errEINVAL
  return .ok out

/-! ## The user's `struct sock_fprog` -/

/-- `struct sock_fprog` as `seccomp_set_mode_filter` copied it: the length
    given and the user pointer to the instructions (`none`: NULL). The
    harness's `bad: insns` arm (design 6.1) is a mapped-looking pointer whose
    copy faults: `insnsFault`. When the pointer is good, the harness supplies
    exactly `len` instructions. -/
structure SockFprog where
  len : Nat
  filter : Option ClassicProg
  insnsFault : Bool := false
  deriving Repr

/-! ## The cache's emulation, decision-free (seccomp.c:736-836) -/

/-- `seccomp_is_const_allow(orig_prog, {nr, arch})`, read directly: the
    uretprobe exception first (:736-754, call 335 on this architecture),
    then the one-register emulation over the un-rewritten program; a load of
    anything but `nr` or `arch`, any other instruction, or running off the
    end answers `false`. This is the reference for the executable check of
    design 4.6 statement 2; the modelled path's version with the C's
    decisions is stream V's. -/
def seccompIsConstAllowPure (prog : ClassicProg) (nr : Int) (arch : UInt32) : Bool := Id.run do
  if nr == NR_URETPROBE then return true
  let nrU : UInt32 := UInt32.ofNat (((nr % 2 ^ 32) + 2 ^ 32) % 2 ^ 32).toNat
  let mut reg : UInt32 := 0
  let mut pc := 0
  let len := prog.size
  -- each iteration advances pc by at least one; `len + 1` iterations suffice
  for _ in [0:len + 1] do
    if pc ≥ len then return false
    let insn := prog[pc]!
    let code := insn.code
    let k := insn.k
    if code == (BPF_LD ||| BPF_W ||| BPF_ABS) then
      if k == 0 then reg := nrU
      else if k == 4 then reg := arch
      else return false
    else if code == (BPF_RET ||| BPF_K) then
      return k == SECCOMP_RET_ALLOW
    else if code == (BPF_JMP ||| BPF_JA) then
      pc := pc + k.toNat
    else if code == (BPF_JMP ||| BPF_JEQ ||| BPF_K) || code == (BPF_JMP ||| BPF_JGE ||| BPF_K)
        || code == (BPF_JMP ||| BPF_JGT ||| BPF_K) || code == (BPF_JMP ||| BPF_JSET ||| BPF_K) then
      let op := bpfOp code
      let res := if op == BPF_JEQ then reg == k
        else if op == BPF_JGE then reg ≥ k
        else if op == BPF_JGT then reg > k
        else (reg &&& k) != 0
      pc := pc + (if res then insn.jt.toNat else insn.jf.toNat)
    else if code == (BPF_ALU ||| BPF_AND ||| BPF_K) then
      reg := reg &&& k
    else return false
    pc := pc + 1
  return false

end Leanux.Seccomp
