/-!
# The checker's and the translation's decision points, and the monad they run in

seccomp stream U (docs/2026-10-12-seccomp-design.md, sections 2.5, 4.2, 4.3,
8): one constructor per C choice point of `net/core/filter.c`'s classic
checker, conversion, migration and creation paths, and of
`kernel/seccomp.c`'s `seccomp_check_filter`. Each names its source line and
the spans that run only on one outcome, as `Leanux.Decision` does; the
per-instruction ones are `repeatable` (design 4.2: one install evaluates
them once per instruction, the check compares the set of pairs).

The shared `Leanux.Decision` type and the allocation-site table belong to
the interface commit (stream I). Until it lands, the walkers of this stream
are written over `SeccompM`, a small typeclass of the recording operations
they need; the instance over the mirror monad `M` maps each constructor
here to its `Decision` constructor, and `Leanux.Seccomp.Local` gives a
self-contained instance for the unit tests and the executable check of
design section 8. Nothing here absorbs a failure: every operation an
instance must provide is one that stops the run or records a step.

Span conventions follow `Leanux/Kernel/Decision.lean`: an operand of one
`||`/`&&` whose body is shared with the other operand carries no span for
that outcome; a `switch` arm is recorded (true) only when taken.
-/

namespace Leanux.Seccomp

/-- The relation of a declared value comparison (as `Leanux.Rel`). -/
inductive SRel where
  | lt | le | gt | ge | eq | ne | flag
  deriving Repr, BEq, DecidableEq

def SRel.name : SRel → String
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq" | .ne => "ne" | .flag => "flag"

structure SDecisionInfo where
  /-- `<C function>.<condition>` -/
  label : String
  file : String
  line : Nat
  whenTrue : List (Nat × Nat) := []
  whenFalse : List (Nat × Nat) := []
  /-- A value comparison: the relation and whether the right-hand operand is
      a compile-time constant. -/
  comparison : Option (SRel × Bool) := none
  repeatable : Bool := false
  deriving Repr

inductive SDecision where
  -- net/core/filter.c: bpf_prog_create_from_user (:1423) and the inlined bpf_check_basics_ok (:1047)
  | basicsFilterNull | basicsLenZero | basicsLenOverMax | createBasicsNotOk
  | createProgAllocNoMem | createCopyFault | createSaveOrig | createStoreOrigErr | createPrepareErr
  -- bpf_prog_store_orig_filter (:1150)
  | storeOrigNoMem | storeOrigFilterNoMem
  -- bpf_prepare_filter (:1329)
  | prepCheckClassicErr | prepHasTrans | prepTransErr | prepNotJited
  -- chk_code_allowed (:981) and bpf_check_classic (:1072)
  | chkCodeOverTable | checkCodeNotAllowed
  | checkCaseDivModK | checkCaseShiftK | checkCaseMem | checkCaseJa | checkCaseJcond | checkCaseLdAbs
  | checkDivModKZero | checkShiftKRange | checkMemIndex | checkJaRange | checkJtRange | checkJfRange
  | checkAncFound | checkAncNotFound | checkAncOffset | checkLastRet
  -- check_load_and_stores (:928)
  | clsMasksNoMem | clsCaseStore | clsCaseLoad | clsCaseJa | clsCaseJcond | clsLoadUnstored
  -- kernel/seccomp.c: seccomp_check_filter (:280)
  | scfCaseLdAbsW | scfCaseLdLen | scfCaseLdxLen | scfCaseAllowed | scfCaseDefault
  | scfCtxOffsetRange | scfCtxMisaligned
  -- bpf_convert_filter (:576)
  | convLenNonpositive | convLenOverMax | convHasNewProg | convAddrsNoMem
  | convPrologue | convSeenLdAbs | convHasAddrs
  | convCaseAluLoad | convCaseJa | convCaseJcond | convCaseLdxMsh | convCaseRet | convCaseStore
  | convCaseLoadMem | convCaseImm | convCaseTax | convCaseTxa | convCaseLen | convCaseLdxAbsW | convCaseDefault
  | convAluClassLd | convAluModeAbs | convAluClassLd2 | convCodeDivX | convCodeModX
  | convJmpSrcK | convJmpKNegative | convJmpSrcX | convJfZero | convJtZero
  | convJtZeroJeq | convJtZeroJgt | convJtZeroJge | convJtZeroDefault
  -- BPF_EMIT_JMP (:706-720), expanded at :725 (JA), :757 (jf == 0), :778 (jt == 0), :785 and :790 (jmp_rest)
  | emitTargetOverLenJa | emitTargetNegativeJa | emitHasAddrsJa | emitOffBelowMinJa | emitOffAboveMaxJa
  | emitTargetOverLenJf | emitTargetNegativeJf | emitHasAddrsJf | emitOffBelowMinJf | emitOffAboveMaxJf
  | emitTargetOverLenJt | emitTargetNegativeJt | emitHasAddrsJt | emitOffBelowMinJt | emitOffAboveMaxJt
  | emitTargetOverLenRest | emitTargetNegativeRest | emitHasAddrsRest | emitOffBelowMinRest | emitOffAboveMaxRest
  | emitTargetOverLenRestJa | emitTargetNegativeRestJa | emitHasAddrsRestJa | emitOffBelowMinRestJa | emitOffAboveMaxRestJa
  | convRetIsK | convStoreHasNewProg | convStackDepthBelow | convEmitCopy
  | convOnlyLength | convSeenLdAbsLen | convPassChanged | convPassOverflow
  -- bpf_migrate_filter (:1259)
  | migOldProgNoMem | migConvert1Err | migReallocNoMem | migConvert2Err | migSelectRuntimeErr
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The five expansion sites of `BPF_EMIT_JMP` in `bpf_convert_filter`. -/
inductive EmitSite where
  | ja | jfZero | jtZero | rest | restJa
  deriving Repr, BEq, DecidableEq

private def fc := "net/core/filter.c"
private def sc := "kernel/seccomp.c"

private def d (label file : String) (line : Nat) (t f : List (Nat × Nat)) : SDecisionInfo :=
  { label, file, line, whenTrue := t, whenFalse := f }

/-- A value comparison. -/
private def c (label file : String) (line : Nat) (rel : SRel) (constRhs : Bool)
    (t f : List (Nat × Nat)) : SDecisionInfo :=
  { label, file, line, whenTrue := t, whenFalse := f, comparison := some (rel, constRhs) }

private def rep (i : SDecisionInfo) : SDecisionInfo := { i with repeatable := true }

def SDecision.info : SDecision → SDecisionInfo
  -- bpf_check_basics_ok, inlined into bpf_prog_create_from_user; `flen == 0 ||
  -- flen > BPF_MAXINSNS` is one line, the first operand's body is shared
  -- a pointer test: no operands (the mirror does not hold user addresses)
  | .basicsFilterNull => d "bpf_check_basics_ok.filter_null" fc 1050 [(1051, 1051)] [(1052, 1052)]
  | .basicsLenZero => c "bpf_check_basics_ok.flen_zero" fc 1052 .eq true [] []
  | .basicsLenOverMax => c "bpf_check_basics_ok.flen_over_max" fc 1052 .gt true [(1053, 1053)] [(1055, 1055)]
  | .createBasicsNotOk => d "bpf_prog_create_from_user.basics_not_ok" fc 1431 [(1432, 1432)] [(1434, 1434)]
  | .createProgAllocNoMem => d "bpf_prog_create_from_user.prog_alloc_nomem" fc 1435 [(1436, 1436)] [(1438, 1438)]
  | .createCopyFault => d "bpf_prog_create_from_user.copy_from_user_fault" fc 1438 [(1439, 1440)] [(1442, 1446)]
  | .createSaveOrig => d "bpf_prog_create_from_user.save_orig" fc 1446 [(1447, 1448)] []
  | .createStoreOrigErr => d "bpf_prog_create_from_user.store_orig_err" fc 1448 [(1449, 1450)] [(1457, 1457)]
  | .createPrepareErr => d "bpf_prog_create_from_user.prepare_err" fc 1458 [(1459, 1459)] [(1461, 1462)]
  | .storeOrigNoMem => d "bpf_prog_store_orig_filter.fkprog_nomem" fc 1157 [(1158, 1158)] [(1160, 1163)]
  | .storeOrigFilterNoMem => d "bpf_prog_store_orig_filter.filter_nomem" fc 1165 [(1166, 1167)] [(1170, 1170)]
  | .prepCheckClassicErr => d "bpf_prepare_filter.check_classic_err" fc 1338 [(1339, 1340)] [(1346, 1346)]
  | .prepHasTrans => d "bpf_prepare_filter.has_trans" fc 1346 [(1347, 1347)] []
  | .prepTransErr => d "bpf_prepare_filter.trans_err" fc 1348 [(1349, 1350)] [(1357, 1357)]
  | .prepNotJited => d "bpf_prepare_filter.not_jited" fc 1362 [(1363, 1363)] []
  -- chk_code_allowed: `code_to_probe >= ARRAY_SIZE(codes)`, 0xb2 (the table's
  -- last initialised index is BPF_LDX | BPF_B | BPF_MSH = 0xb1)
  | .chkCodeOverTable => rep <| c "chk_code_allowed.over_table" fc 1041 .ge true [(1042, 1042)] [(1044, 1044)]
  | .checkCodeNotAllowed => rep <| d "bpf_check_classic.code_not_allowed" fc 1083 [(1084, 1084)] [(1087, 1087)]
  | .checkCaseDivModK => rep <| d "bpf_check_classic.case_div_mod_k" fc 1088 [(1091, 1091)] []
  | .checkCaseShiftK => rep <| d "bpf_check_classic.case_shift_k" fc 1094 [(1096, 1096)] []
  | .checkCaseMem => rep <| d "bpf_check_classic.case_mem" fc 1099 [(1104, 1104)] []
  | .checkCaseJa => rep <| d "bpf_check_classic.case_ja" fc 1107 [(1112, 1112)] []
  | .checkCaseJcond => rep <| d "bpf_check_classic.case_jcond" fc 1115 [(1124, 1124)] []
  | .checkCaseLdAbs => rep <| d "bpf_check_classic.case_ld_abs" fc 1128 [(1131, 1133)] []
  | .checkDivModKZero => rep <| c "bpf_check_classic.div_mod_k_zero" fc 1091 .eq true [(1092, 1092)] [(1093, 1093)]
  | .checkShiftKRange => rep <| c "bpf_check_classic.shift_k_over_32" fc 1096 .ge true [(1097, 1097)] [(1098, 1098)]
  | .checkMemIndex => rep <| c "bpf_check_classic.mem_over_memwords" fc 1104 .ge true [(1105, 1105)] [(1106, 1106)]
  | .checkJaRange => rep <| c "bpf_check_classic.ja_over_end" fc 1112 .ge false [(1113, 1113)] [(1114, 1114)]
  -- `pc + jt + 1 >= flen || pc + jf + 1 >= flen` over two lines, body shared
  | .checkJtRange => rep <| c "bpf_check_classic.jt_over_end" fc 1124 .ge false [] [(1125, 1125)]
  | .checkJfRange => rep <| c "bpf_check_classic.jf_over_end" fc 1125 .ge false [(1126, 1126)] [(1127, 1127)]
  | .checkAncFound => rep <| c "bpf_check_classic.anc_found" fc 1132 .flag true [(1133, 1133)] []
  -- `anc_found == false && ftest->k >= SKF_AD_OFF` on one line
  | .checkAncNotFound => rep <| c "bpf_check_classic.anc_not_found" fc 1135 .eq true [] []
  | .checkAncOffset => rep <| c "bpf_check_classic.k_over_skf_ad_off" fc 1135 .ge true [(1136, 1136)] []
  -- the switch on the last instruction's code: both arms share one body
  | .checkLastRet => d "bpf_check_classic.last_is_ret" fc 1141 [(1144, 1144)] [(1147, 1147)]
  | .clsMasksNoMem => d "check_load_and_stores.masks_nomem" fc 936 [(937, 937)] [(939, 939)]
  | .clsCaseStore => rep <| d "check_load_and_stores.case_store" fc 945 [(947, 948)] []
  | .clsCaseLoad => rep <| d "check_load_and_stores.case_load" fc 949 [(951, 951)] []
  | .clsCaseJa => rep <| d "check_load_and_stores.case_ja" fc 956 [(958, 960)] []
  | .clsCaseJcond => rep <| d "check_load_and_stores.case_jcond" fc 961 [(970, 973)] []
  | .clsLoadUnstored => rep <| c "check_load_and_stores.load_unstored" fc 951 .flag false [(952, 953)] [(955, 955)]
  | .scfCaseLdAbsW => rep <| d "seccomp_check_filter.case_ld_w_abs" sc 289 [(290, 292)] []
  | .scfCaseLdLen => rep <| d "seccomp_check_filter.case_ld_w_len" sc 295 [(296, 298)] []
  | .scfCaseLdxLen => rep <| d "seccomp_check_filter.case_ldx_w_len" sc 299 [(300, 302)] []
  | .scfCaseAllowed => rep <| d "seccomp_check_filter.case_allowed" sc 304 [(342, 342)] []
  | .scfCaseDefault => rep <| d "seccomp_check_filter.case_default" sc 343 [(344, 344)] []
  -- `k >= sizeof(struct seccomp_data) || k & 3` on one line
  | .scfCtxOffsetRange => rep <| c "seccomp_check_filter.k_over_data_size" sc 292 .ge true [] []
  | .scfCtxMisaligned => rep <| c "seccomp_check_filter.k_misaligned" sc 292 .flag true [(293, 293)] [(294, 294)]
  -- `len <= 0 || len > BPF_MAXINSNS` on one line
  | .convLenNonpositive => c "bpf_convert_filter.len_nonpositive" fc 589 .le true [] []
  | .convLenOverMax => c "bpf_convert_filter.len_over_max" fc 589 .gt true [(590, 590)] [(592, 592)]
  | .convHasNewProg => d "bpf_convert_filter.has_new_prog" fc 592 [(593, 596)] []
  | .convAddrsNoMem => d "bpf_convert_filter.addrs_nomem" fc 596 [(597, 597)] []
  | .convPrologue => rep <| d "bpf_convert_filter.prologue" fc 605 [(609, 617)] [(633, 633)]
  | .convSeenLdAbs => rep <| d "bpf_convert_filter.seen_ld_abs" fc 617 [(622, 630)] []
  | .convHasAddrs => rep <| d "bpf_convert_filter.has_addrs" fc 640 [(641, 641)] []
  | .convCaseAluLoad => rep <| d "bpf_convert_filter.case_alu_load" fc 645 [(676, 676)] []
  | .convCaseJa => rep <| d "bpf_convert_filter.case_ja" fc 722 [(723, 725)] []
  | .convCaseJcond => rep <| d "bpf_convert_filter.case_jcond" fc 728 [(736, 736)] []
  | .convCaseLdxMsh => rep <| d "bpf_convert_filter.case_ldx_msh" fc 794 [(795, 806)] []
  | .convCaseRet => rep <| d "bpf_convert_filter.case_ret" fc 822 [(824, 824)] []
  | .convCaseStore => rep <| d "bpf_convert_filter.case_store" fc 831 [(833, 836)] []
  | .convCaseLoadMem => rep <| d "bpf_convert_filter.case_load_mem" fc 846 [(848, 851)] []
  | .convCaseImm => rep <| d "bpf_convert_filter.case_imm" fc 855 [(857, 858)] []
  | .convCaseTax => rep <| d "bpf_convert_filter.case_tax" fc 862 [(863, 863)] []
  | .convCaseTxa => rep <| d "bpf_convert_filter.case_txa" fc 867 [(868, 868)] []
  | .convCaseLen => rep <| d "bpf_convert_filter.case_len" fc 872 [(874, 876)] []
  | .convCaseLdxAbsW => rep <| d "bpf_convert_filter.case_ldx_abs_w" fc 880 [(882, 882)] []
  | .convCaseDefault => rep <| d "bpf_convert_filter.case_default" fc 886 [(887, 887)] []
  -- `BPF_CLASS(fp->code) == BPF_LD && BPF_MODE(fp->code) == BPF_ABS && convert_bpf_extensions(...)`
  | .convAluClassLd => rep <| c "bpf_convert_filter.alu_class_ld" fc 676 .eq true [] [(680, 680)]
  | .convAluModeAbs => rep <| c "bpf_convert_filter.alu_mode_abs" fc 677 .eq true [] []
  | .convAluClassLd2 => rep <| c "bpf_convert_filter.alu_class_ld_abs_load" fc 680 .eq true [] [(686, 686)]
  -- `fp->code == DIV|X || fp->code == MOD|X` over two lines
  | .convCodeDivX => rep <| c "bpf_convert_filter.code_div_x" fc 686 .eq true [] [(687, 687)]
  | .convCodeModX => rep <| c "bpf_convert_filter.code_mod_x" fc 687 .eq true [(688, 694)] [(697, 697)]
  -- `BPF_SRC(fp->code) == BPF_K && (int) fp->k < 0` on one line
  | .convJmpSrcK => rep <| c "bpf_convert_filter.jmp_src_k" fc 736 .eq true [] []
  | .convJmpKNegative => rep <| c "bpf_convert_filter.jmp_k_negative" fc 736 .lt true [(741, 745)] [(747, 750)]
  | .convJmpSrcX => rep <| c "bpf_convert_filter.jmp_src_is_x" fc 750 .eq true [] []
  | .convJfZero => rep <| c "bpf_convert_filter.jf_zero" fc 754 .eq true [(755, 758)] [(762, 762)]
  | .convJtZero => rep <| c "bpf_convert_filter.jt_zero" fc 762 .eq true [(763, 763)] []
  | .convJtZeroJeq => rep <| d "bpf_convert_filter.jt_zero_case_jeq" fc 764 [(765, 766)] []
  | .convJtZeroJgt => rep <| d "bpf_convert_filter.jt_zero_case_jgt" fc 767 [(768, 769)] []
  | .convJtZeroJge => rep <| d "bpf_convert_filter.jt_zero_case_jge" fc 770 [(771, 772)] []
  | .convJtZeroDefault => rep <| d "bpf_convert_filter.jt_zero_case_default" fc 773 [(774, 774)] []
  -- BPF_EMIT_JMP: the statements of the macro take the expansion line; its
  -- outcomes are told apart by the operands, not by lines
  | .emitTargetOverLenJa => rep <| c "bpf_convert_filter.emit_ja.target_over_len" fc 725 .ge false [] []
  | .emitTargetNegativeJa => rep <| c "bpf_convert_filter.emit_ja.target_negative" fc 725 .lt true [] []
  | .emitHasAddrsJa => rep <| d "bpf_convert_filter.emit_ja.has_addrs" fc 725 [] []
  | .emitOffBelowMinJa => rep <| c "bpf_convert_filter.emit_ja.off_below_min" fc 725 .lt true [] []
  | .emitOffAboveMaxJa => rep <| c "bpf_convert_filter.emit_ja.off_above_max" fc 725 .gt true [] []
  | .emitTargetOverLenJf => rep <| c "bpf_convert_filter.emit_jf_zero.target_over_len" fc 757 .ge false [] []
  | .emitTargetNegativeJf => rep <| c "bpf_convert_filter.emit_jf_zero.target_negative" fc 757 .lt true [] []
  | .emitHasAddrsJf => rep <| d "bpf_convert_filter.emit_jf_zero.has_addrs" fc 757 [] []
  | .emitOffBelowMinJf => rep <| c "bpf_convert_filter.emit_jf_zero.off_below_min" fc 757 .lt true [] []
  | .emitOffAboveMaxJf => rep <| c "bpf_convert_filter.emit_jf_zero.off_above_max" fc 757 .gt true [] []
  | .emitTargetOverLenJt => rep <| c "bpf_convert_filter.emit_jt_zero.target_over_len" fc 778 .ge false [] []
  | .emitTargetNegativeJt => rep <| c "bpf_convert_filter.emit_jt_zero.target_negative" fc 778 .lt true [] []
  | .emitHasAddrsJt => rep <| d "bpf_convert_filter.emit_jt_zero.has_addrs" fc 778 [] []
  | .emitOffBelowMinJt => rep <| c "bpf_convert_filter.emit_jt_zero.off_below_min" fc 778 .lt true [] []
  | .emitOffAboveMaxJt => rep <| c "bpf_convert_filter.emit_jt_zero.off_above_max" fc 778 .gt true [] []
  | .emitTargetOverLenRest => rep <| c "bpf_convert_filter.emit_rest.target_over_len" fc 785 .ge false [] []
  | .emitTargetNegativeRest => rep <| c "bpf_convert_filter.emit_rest.target_negative" fc 785 .lt true [] []
  | .emitHasAddrsRest => rep <| d "bpf_convert_filter.emit_rest.has_addrs" fc 785 [] []
  | .emitOffBelowMinRest => rep <| c "bpf_convert_filter.emit_rest.off_below_min" fc 785 .lt true [] []
  | .emitOffAboveMaxRest => rep <| c "bpf_convert_filter.emit_rest.off_above_max" fc 785 .gt true [] []
  | .emitTargetOverLenRestJa => rep <| c "bpf_convert_filter.emit_rest_ja.target_over_len" fc 790 .ge false [] []
  | .emitTargetNegativeRestJa => rep <| c "bpf_convert_filter.emit_rest_ja.target_negative" fc 790 .lt true [] []
  | .emitHasAddrsRestJa => rep <| d "bpf_convert_filter.emit_rest_ja.has_addrs" fc 790 [] []
  | .emitOffBelowMinRestJa => rep <| c "bpf_convert_filter.emit_rest_ja.off_below_min" fc 790 .lt true [] []
  | .emitOffAboveMaxRestJa => rep <| c "bpf_convert_filter.emit_rest_ja.off_above_max" fc 790 .gt true [] []
  | .convRetIsK => rep <| c "bpf_convert_filter.ret_is_k" fc 824 .eq true [(825, 826)] []
  -- `new_prog && new_prog->aux->stack_depth < stack_off` on one line
  | .convStoreHasNewProg => rep <| d "bpf_convert_filter.store_has_new_prog" fc 841 [] []
  | .convStackDepthBelow => rep <| c "bpf_convert_filter.stack_depth_below" fc 841 .lt false [(842, 842)] [(843, 843)]
  | .convEmitCopy => rep <| d "bpf_convert_filter.emit_copy" fc 891 [(892, 893)] []
  | .convOnlyLength => rep <| d "bpf_convert_filter.only_length" fc 897 [(899, 902)] [(905, 905)]
  | .convSeenLdAbsLen => rep <| d "bpf_convert_filter.seen_ld_abs_len" fc 900 [(901, 901)] [(902, 902)]
  | .convPassChanged => rep <| c "bpf_convert_filter.pass_changed" fc 906 .ne false [(907, 908)] [(913, 915)]
  | .convPassOverflow => rep <| c "bpf_convert_filter.pass_over_2" fc 908 .gt true [(909, 909)] [(910, 910)]
  | .migOldProgNoMem => d "bpf_migrate_filter.old_prog_nomem" fc 1279 [(1280, 1281)] [(1285, 1285)]
  | .migConvert1Err => d "bpf_migrate_filter.convert1_err" fc 1287 [(1288, 1288)] [(1291, 1292)]
  | .migReallocNoMem => d "bpf_migrate_filter.realloc_nomem" fc 1293 [(1297, 1299)] [(1302, 1305)]
  | .migConvert2Err => d "bpf_migrate_filter.convert2_err" fc 1307 [(1313, 1313)] [(1315, 1315)]
  | .migSelectRuntimeErr => d "bpf_migrate_filter.select_runtime_err" fc 1316 [(1317, 1317)] [(1319, 1320)]

def SDecision.all : List SDecision :=
  (List.range 512).filterMap fun i =>
    let x := SDecision.ofNat i
    if x.ctorIdx == i then some x else none

/-- The allocation sites of one install on these paths (design 3.1, sites
    2-11), in the order the C reaches them. `recorded` says whether the
    kind-305 hook sees the site: the page and percpu allocations under
    `kernel/bpf/core.c` are unrecorded by construction and assumed to
    succeed (their `-ENOMEM` arms are modelled, unexercised). -/
inductive SAllocSite where
  /-- `bpf_prog_alloc_no_stats` `__vmalloc(size)` (core.c:105): pages via mm/vmalloc.c -/
  | bpfProgAllocImage
  /-- `bpf_prog_alloc_no_stats` `kzalloc(aux)` (core.c:109) -/
  | bpfProgAllocAux
  /-- `bpf_prog_alloc_no_stats` `alloc_percpu_gfp(active)` (core.c:114) -/
  | bpfProgAllocActive
  /-- `bpf_prog_alloc` `alloc_percpu_gfp(stats)` (core.c:151) -/
  | bpfProgAllocStats
  /-- `bpf_prog_store_orig_filter` `kmalloc(fkprog)` (filter.c:1156) -/
  | kmallocOrigFkprog
  /-- `bpf_prog_store_orig_filter` `kmemdup(filter)` (filter.c:1163) -/
  | kmemdupOrigFilter
  /-- `check_load_and_stores` `kmalloc_array(masks)` (filter.c:935) -/
  | kmallocArrayMasks
  /-- `bpf_migrate_filter` `kmemdup_array(old_prog)` (filter.c:1277) -/
  | kmemdupArrayOldProg
  /-- `bpf_prog_realloc` `__vmalloc` (core.c:260), below the cut: its page
      test is not a mirror decision -/
  | bpfProgReallocImage
  /-- `bpf_convert_filter`'s second pass `kcalloc(addrs)` (filter.c:594) -/
  | kcallocAddrs
  deriving Repr, BEq, DecidableEq, Inhabited

structure SAllocSiteInfo where
  label : String
  file : String
  line : Nat
  recorded : Bool

def SAllocSite.info : SAllocSite → SAllocSiteInfo
  | .bpfProgAllocImage => ⟨"bpfProgAllocImage", "kernel/bpf/core.c", 105, false⟩
  | .bpfProgAllocAux => ⟨"bpfProgAllocAux", "kernel/bpf/core.c", 109, true⟩
  | .bpfProgAllocActive => ⟨"bpfProgAllocActive", "kernel/bpf/core.c", 114, false⟩
  | .bpfProgAllocStats => ⟨"bpfProgAllocStats", "kernel/bpf/core.c", 151, false⟩
  | .kmallocOrigFkprog => ⟨"kmallocOrigFkprog", "net/core/filter.c", 1156, true⟩
  | .kmemdupOrigFilter => ⟨"kmemdupOrigFilter", "net/core/filter.c", 1163, true⟩
  | .kmallocArrayMasks => ⟨"kmallocArrayMasks", "net/core/filter.c", 935, true⟩
  | .kmemdupArrayOldProg => ⟨"kmemdupArrayOldProg", "net/core/filter.c", 1277, true⟩
  | .bpfProgReallocImage => ⟨"bpfProgReallocImage", "kernel/bpf/core.c", 260, false⟩
  | .kcallocAddrs => ⟨"kcallocAddrs", "net/core/filter.c", 594, true⟩

def SAllocSite.all : List SAllocSite :=
  [.bpfProgAllocImage, .bpfProgAllocAux, .bpfProgAllocActive, .bpfProgAllocStats,
   .kmallocOrigFkprog, .kmemdupOrigFilter, .kmallocArrayMasks, .kmemdupArrayOldProg,
   .bpfProgReallocImage, .kcallocAddrs]

/-- The recording operations the checker and the translation need. The
    instance over the mirror monad maps each `SDecision` to its `Decision`
    and each `SAllocSite` to its `AllocSite`; `Leanux.Seccomp.Local` is the
    self-contained instance. Every operation either records a step or stops
    the run: no instance may answer a stop with a default. -/
class SeccompM (m : Type → Type) extends Monad m where
  /-- Record a C decision point with its outcome and return the outcome. -/
  branch : SDecision → Bool → m Bool
  /-- Record a C value comparison with the two values the C compares. -/
  branchCmp : SDecision → Bool → Int → Int → m Bool
  /-- An allocation outcome at a site: the recorded answer, or `true` for an
      unrecorded site. -/
  alloc : SAllocSite → m Bool
  /-- The next kind-309 record: the word of one emitted `bpf_insn` (design
      3.3), or `none` when the run has no records (the domain filter). -/
  translatedInsn : m (Option Nat)
  /-- The kind-309 length record that follows the instructions. -/
  translatedLen : m (Option Nat)
  /-- The records disagree with the mirror (`Stop.hidden`). -/
  recordMismatch {α : Type} : String → m α
  /-- The C leaves the modelled domain (`Stop.outsideDomain`). -/
  unsupported {α : Type} : String → m α
  /-- A mirror defect: a path the design proves dead was reached (`Stop.invariant`). -/
  invariant {α : Type} : String → m α

export SeccompM (branch branchCmp alloc translatedInsn translatedLen recordMismatch unsupported invariant)

section Helpers
variable {m : Type → Type} [SeccompM m]

def cmpEq (d : SDecision) (a b : Int) : m Bool := branchCmp d (a == b) a b
def cmpNe (d : SDecision) (a b : Int) : m Bool := branchCmp d (a != b) a b
def cmpLt (d : SDecision) (a b : Int) : m Bool := branchCmp d (a < b) a b
def cmpLe (d : SDecision) (a b : Int) : m Bool := branchCmp d (a ≤ b) a b
def cmpGt (d : SDecision) (a b : Int) : m Bool := branchCmp d (a > b) a b
def cmpGe (d : SDecision) (a b : Int) : m Bool := branchCmp d (a ≥ b) a b
/-- A flag test `a & b`, reported with the C's operands. -/
def cmpFlag (d : SDecision) (a b : Int) : m Bool := branchCmp d ((a.toNat &&& b.toNat) != 0) a b

end Helpers

/-- The values these paths return, as the C spells them (`-EINVAL` ...).
    These leaf modules do not import `Leanux.Kernel.Defs`, whose `EINVAL`
    etc. are the positive numbers. -/
def errEINVAL : Int := -22
def errENOMEM : Int := -12
def errEFAULT : Int := -14

/-- A `u32` as the C compares it. -/
def u32 (x : UInt32) : Int := x.toNat
/-- A `u32` read as `int`. -/
def s32 (x : UInt32) : Int := if x.toNat ≥ 2 ^ 31 then (x.toNat : Int) - 2 ^ 32 else x.toNat

end Leanux.Seccomp
