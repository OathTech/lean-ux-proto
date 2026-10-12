#!/usr/bin/env python3
"""Writes the seccomp corpus into corpus/seccomp and the negative controls into
corpus/seccomp-controls (docs/2026-10-12-seccomp-design.md section 7), in the
epoll corpus's style: the program listings are in the trace files, and each
operation's comment here says what Linux 6.12.110 does with the kernel/seccomp.c
or net/core/filter.c line that decides it. A comment is a statement of intent;
the check compares the mirror against the real kernel. The output is
deterministic (`--check` verifies the committed files without writing).

Conventions (design 6.2): every accepted filter starts with the canonical
prologue, which loads `arch` and `nr` and constant-allows every number outside
the probe set {102, 104, 107, 108, 1000, 335}, so the harness's own calls are
cache hits; a filter that may kill (the validator's scan) is probed in a
sandboxed child (`seccomp_child`); strict mode is child-only. Stream W measured
(design 7, 2026-10-12) that an install may hold at most 768 classic
instructions (the comparison area overflows at 1024) and that each child probe
costs about 1 MB of console output, so no program here is longer than 768 and
no trace holds more than three child probes.
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness.trace import validate_trace, filter_may_kill  # noqa: E402

OUT = ROOT / "corpus" / "seccomp"
CONTROLS = ROOT / "corpus" / "seccomp-controls"

# include/uapi/linux/bpf_common.h: class | size/op | mode/src
LD_W_ABS, LD_H_ABS, LD_B_ABS, LD_W_LEN, LDX_W_LEN = 0x20, 0x28, 0x30, 0x80, 0x81
LD_IMM, LDX_IMM, LD_MEM, LDX_MEM, LDX_B_MSH = 0x00, 0x01, 0x60, 0x61, 0xb1
ST, STX, RET_K, RET_A, JA = 0x02, 0x03, 0x06, 0x16, 0x05
JEQ_K, JEQ_X, JGT_K, JGT_X, JGE_K, JGE_X, JSET_K, JSET_X = 0x15, 0x1d, 0x25, 0x2d, 0x35, 0x3d, 0x45, 0x4d
ADD_K, ADD_X, SUB_K, SUB_X, MUL_K, MUL_X, DIV_K, DIV_X = 0x04, 0x0c, 0x14, 0x1c, 0x24, 0x2c, 0x34, 0x3c
OR_K, OR_X, AND_K, AND_X, XOR_K, XOR_X = 0x44, 0x4c, 0x54, 0x5c, 0xa4, 0xac
LSH_K, LSH_X, RSH_K, RSH_X, NEG, MOD_K, MOD_X = 0x64, 0x6c, 0x74, 0x7c, 0x84, 0x94, 0x9c
TAX, TXA = 0x07, 0x87
# include/uapi/linux/seccomp.h: the return actions (the high half) and data
ALLOW, LOG, TRACE, USER_NOTIF = 0x7fff0000, 0x7ffc0000, 0x7ff00000, 0x7fc00000
ERRNO, TRAP, KILL_THREAD, KILL_PROCESS = 0x00050000, 0x00030000, 0x00000000, 0x80000000
X86_64 = 0xc000003e          # AUDIT_ARCH_X86_64
NR, ARCH, IP = 0, 4, 8       # struct seccomp_data offsets; args[k] at 16 + 8k
U32 = 2**32 - 1
SKF_AD_OFF = 0xfffff000      # the ancillary load space (include/uapi/linux/filter.h)
NB = 0o4000                  # O_NONBLOCK = EFD_NONBLOCK
# harness/linux.py treats these errnos as the guest's infrastructure failing
# (EINTR, ENOMEM, ENFILE, the restart codes), so no ERRNO data here is one
RESERVED_ERRNO = {4, 12, 23, 512, 513, 514, 516}


def arg(k, high=False):
    return 16 + 8 * k + (4 if high else 0)


def insn(code, jt=0, jf=0, k=0):
    return [code, jt, jf, k]


def ld(k):
    return insn(LD_W_ABS, k=k)


def ret(k):
    return insn(RET_K, k=k)


def jeq(k, jt, jf):
    return insn(JEQ_K, jt, jf, k)


def prologue(cases, default=ALLOW, arch_check=True):
    """The canonical prologue (design 6.2 rule 1): `arch` loaded and tested
    (a foreign arch is allowed, never taken on this oracle), `nr` loaded, one
    `JEQ` per probe number falling into its body (every body ends in a RET or
    jumps within itself), and `RET ALLOW` for every other number. Every
    instruction on a non-probe number's path is one `seccomp_is_const_allow`
    follows (:762-836), so the cache marks it allowed."""
    program = [ld(ARCH), jeq(X86_64, 1, 0), ret(ALLOW)] if arch_check else []
    program.append(ld(NR))
    for nr, body in cases:
        if len(body) <= 255:
            program.append(jeq(nr, 0, len(body)))
        else:   # a jf is a byte: a long body is skipped through JA's 32-bit k
            program += [jeq(nr, 1, 0), insn(JA, k=len(body))]
        program += body
    program.append(ret(default))
    return program


def long_filter(nr, action, length=768, reachable=True):
    """A `length`-instruction filter: the prologue, then for `nr` a chain of
    `JA 0` ending in `RET action`. With `reachable` false the chain sits
    behind the RET (dead but checked), so the cache's emulation for `nr` is
    short."""
    pad = length - 7                       # the prologue's three, LD nr, JEQ, JA and RET ALLOW
    body = [insn(JA)] * (pad - 1) + [ret(action)] if reachable else [ret(action)] + [insn(JA)] * (pad - 1)
    program = prologue([(nr, body)])
    assert len(program) == length, len(program)
    return program


# ---- operations (contracts/trace-v1.md, Seccomp) ---------------------------

def install(program, via="seccomp", flags=(), **extra):
    op = {"op": "seccomp_install", "via": via, "flags": list(flags), "filter": program}
    op.update(extra)
    return op


def probe(nr, where="self", args=None, strict=None):
    op = {"op": "seccomp_probe", "nr": nr, "where": where}
    if args is not None:
        op["args"] = list(args) + [0] * (6 - len(args))
    if strict is not None:
        op["strict"] = strict
    return op


def child(nr, args=None, strict=None):
    return probe(nr, "child", args, strict)


def prctl(cmd, **args):
    op = {"op": "seccomp_prctl", "cmd": cmd}
    op.update(args)
    return op


def capdrop():
    return {"op": "seccomp_capdrop"}


def query(cmd, action=None, flags=None):
    op = {"op": "seccomp_query", "cmd": cmd}
    if action is not None:
        op["action"] = action
    if flags is not None:
        op["flags"] = flags
    return op


def eventfd2(init=0, flags=NB):
    return {"op": "eventfd2", "init": init, "flags": flags}


def pipe2(flags=NB):
    return {"op": "pipe2", "flags": flags}


def write(fd, count=8, value=1):
    return {"op": "write", "fd": fd, "count": count, "value": str(value)}


def read(fd, count=8):
    return {"op": "read", "fd": fd, "count": count}


def close(fd):
    return {"op": "close", "fd": fd}


def ref(i):
    return {"ref": i}


def end(i, e):
    return {"pipe": i, "end": e}


TRACES, CONTROL_TRACES = {}, {}


def trace(name, ops, table=TRACES, **extra):
    t = dict(version=1, id=name, ops=ops, **extra)
    if any(op["op"] == "seccomp_probe" and op["where"] == "child" for op in ops):
        t["seccomp_child"] = True
    table[name] = t


ALLOW_ALL = prologue([])
RET_ALLOW = [ret(ALLOW)]

# ---- install (2.4) --------------------------------------------------------

# The RET ALLOW singleton: every number is const-allow (:762-836), so each
# probe is a cache hit; 335 is the uretprobe exception, allowed before the
# program and -ENOSYS from the table (UPROBES absent); the mode reads 2.
trace("s_allow_singleton", [
    install(RET_ALLOW),                        # 0: 0
    probe(102),                                # 1: 0
    probe(335),                                # 2: -ENOSYS
    prctl("get_seccomp"),                      # 3: 2 (SECCOMP_MODE_FILTER)
])

# The canonical prologue alone: 102 and 108 are cache hits; 1000 is outside
# the cache's range (0..462) so the program runs and answers ALLOW, and the
# table answers -ENOSYS (the cache miss witnessed).
trace("s_prologue_alone", [
    install(ALLOW_ALL),                        # 0: 0
    probe(102),                                # 1: 0
    probe(1000),                               # 2: -ENOSYS
    probe(108),                                # 3: 0
    prctl("get_seccomp"),                      # 4: 2
])

# A NULL instruction pointer: bpf_check_basics_ok (filter.c:1050) after the
# length test passed (:672); nothing is installed.
trace("s_null_program", [
    install(None),                             # 0: -EINVAL
    prctl("get_seccomp"),                      # 1: 0
])

# The length arms of seccomp_prepare_filter (:672): 0 and 4097 before any
# copy. (4096 as a real program is out of reach: stream W measured the
# comparison area overflowing at 1024 instructions; s_len_768 is the long
# install.)
trace("s_len_arms", [
    install(RET_ALLOW, len=0),                 # 0: -EINVAL
    install(RET_ALLOW, len=4097),              # 1: -EINVAL
    prctl("get_seccomp"),                      # 2: 0
])

# The longest install the harness carries: 768 instructions, a JA chain for
# 102 ending in ERRNO 7 (the second convert pass walks every instruction);
# 104 is a cache hit.
trace("s_len_768", [
    install(long_filter(102, ERRNO | 7)),      # 0: 0
    probe(102),                                # 1: -7 (E2BIG, the data)
    probe(104),                                # 2: 0
])

# The two -EFAULT arms: the sock_fprog pointer (seccomp_prepare_user_filter
# :714-733) and the instruction pointer (bpf_prog_create_from_user,
# filter.c:1446).
trace("s_bad_pointers", [
    install(RET_ALLOW, bad="fprog"),           # 0: -EFAULT
    install(RET_ALLOW, bad="insns"),           # 1: -EFAULT
    prctl("get_seccomp"),                      # 2: 0
])

# The flag arms of seccomp_set_mode_filter, in the C's order: a bit outside
# SECCOMP_FILTER_FLAG_MASK (:1957), TSYNC with NEW_LISTENER and no TSYNC_ESRCH
# (:1967-1970), WAIT_KILLABLE_RECV without NEW_LISTENER (:1976-1978); then
# the accepted flags LOG and SPEC_ALLOW (the speculation mitigation is a cut).
trace("s_flag_arms", [
    install(RET_ALLOW, flags=[64]),            # 0: -EINVAL
    install(RET_ALLOW, flags=[256]),           # 1: -EINVAL
    install(RET_ALLOW, flags=[0x8000]),        # 2: -EINVAL
    install(RET_ALLOW, flags=["tsync", "new_listener"]),   # 3: -EINVAL
    install(RET_ALLOW, flags=["wait_killable_recv"]),      # 4: -EINVAL
    prctl("get_seccomp"),                      # 5: 0
    install(ALLOW_ALL, flags=["spec_allow"]),  # 6: 0
    install(ALLOW_ALL, flags=["log", "spec_allow"]),       # 7: 0
    prctl("get_seccomp"),                      # 8: 2
    probe(102),                                # 9: 0
])

# prctl(PR_SET_SECCOMP): prctl_set_seccomp (kernel/sys.c:2130-2155) maps mode 2
# to SET_MODE_FILTER with flags 0 and every other mode but 1 to -EINVAL; a
# second install chains.
trace("s_prctl_modes", [
    install(ALLOW_ALL, via="prctl", mode=0),   # 0: -EINVAL
    install(ALLOW_ALL, via="prctl", mode=3),   # 1: -EINVAL
    install(ALLOW_ALL, via="prctl", mode=255), # 2: -EINVAL
    prctl("get_seccomp"),                      # 3: 0
    install(ALLOW_ALL, via="prctl"),           # 4: 0 (mode 2)
    prctl("get_seccomp"),                      # 5: 2
    install(prologue([(102, [ret(ERRNO | 3)])]), via="prctl"),   # 6: 0
    probe(102),                                # 7: -3
    probe(104),                                # 8: 0
])

# ---- the checker (2.5), one trace per -EINVAL arm ---------------------------

def rejected(name, program, why):
    """An install the checker refuses: -EINVAL, and the mode stays 0."""
    trace(name, [
        install(program),                      # 0: -EINVAL
        prctl("get_seccomp"),                  # 1: 0
    ])


# chk_code_allowed (filter.c:981-1045): a code outside the table
rejected("s_chk_unknown_code", [insn(0xff), ret(ALLOW)], "chk_code_allowed")
# a code inside the table's range that is not a classic instruction
rejected("s_chk_unknown_code_low", [insn(0x09), ret(ALLOW)], "chk_code_allowed")
# DIV|K and MOD|K with k == 0 (:1086-1090)
rejected("s_chk_div_k_zero", [insn(DIV_K, k=0), ret(ALLOW)], "division by zero")
rejected("s_chk_mod_k_zero", [insn(MOD_K, k=0), ret(ALLOW)], "division by zero")
# LSH|K and RSH|K with k >= 32 (:1091-1095)
rejected("s_chk_lsh_32", [insn(LSH_K, k=32), ret(ALLOW)], "shift")
# a memory cell outside BPF_MEMWORDS (:1096-1103)
rejected("s_chk_st_16", [insn(ST, k=16), ret(ALLOW)], "memory address")
# JA with k >= flen - pc - 1 (:1104-1111)
rejected("s_chk_ja_past_end", [insn(JA, k=1), ret(ALLOW)], "JA past the end")
# a conditional jump's jt or jf past the end (:1112-1124)
rejected("s_chk_jt_past_end", [jeq(0, 1, 0), ret(ALLOW)], "jt past the end")
rejected("s_chk_jf_past_end", [jeq(0, 0, 1), ret(ALLOW)], "jf past the end")
# the last instruction is not RET (:1140-1147)
rejected("s_chk_last_not_ret", [ret(ALLOW), ld(NR)], "last instruction")
# an ancillary offset bpf_anc_helper does not know (:1125-1133)
rejected("s_chk_anc_unknown", [ld(SKF_AD_OFF + 2), ret(ALLOW)], "ancillary")
# a known ancillary offset (SKF_AD_PROTOCOL) passes the classic checker and
# fails seccomp_check_filter's bound (seccomp.c:291)
rejected("s_chk_anc_known", [ld(SKF_AD_OFF), ret(ALLOW)], "seccomp bound")
# seccomp_check_filter (seccomp.c:291): a misaligned CTX load, and one at 64
rejected("s_chk_ctx_misaligned", [ld(1), ret(ALLOW)], "k & 3")
rejected("s_chk_ctx_64", [ld(64), ret(ALLOW)], "k >= sizeof(seccomp_data)")
# codes the classic checker allows and seccomp_check_filter does not (:346):
# the half-word load, LDX|MSH, MOD|X and a non-zero MOD|K
rejected("s_chk_ld_h_abs", [insn(LD_H_ABS, k=0), ret(ALLOW)], "seccomp default")
rejected("s_chk_ldx_msh", [insn(LDX_B_MSH, k=0), ret(ALLOW)], "seccomp default")
rejected("s_chk_mod_x", [insn(LDX_IMM, k=2), insn(LD_IMM, k=5), insn(MOD_X), ret(ALLOW)], "seccomp default")
rejected("s_chk_mod_k", [insn(MOD_K, k=2), ret(ALLOW)], "seccomp default")
# check_load_and_stores (filter.c:928-979): a load of a cell never stored
rejected("s_chk_mem_unstored", [insn(LD_MEM, k=0), ret(ALLOW)], "load before store")
# a cell stored on one path only: the jf edge reaches the load with the cell
# invalid (masks[target] &= memvalid, :955-966)
rejected("s_chk_mem_one_path", [ld(NR), jeq(102, 0, 1), insn(ST, k=3), insn(LD_MEM, k=3), ret(ALLOW)],
         "intersection over incoming edges")

# The LEN rewrite (seccomp.c:296-303): LD|W|LEN and LDX|W|LEN become
# immediate loads of sizeof(struct seccomp_data) = 64, so a program that
# allows iff LEN == 64 allows; the bodies are not const-evaluable, so 102 and
# 104 miss the cache and run.
trace("s_chk_len_rewrite", [
    install(prologue([
        (102, [insn(LD_W_LEN), jeq(64, 0, 1), ret(ALLOW), ret(ERRNO | 1)]),
        (104, [insn(LDX_W_LEN), insn(TXA), jeq(64, 0, 1), ret(ALLOW), ret(ERRNO | 1)]),
    ])),                                       # 0: 0
    probe(102),                                # 1: 0
    probe(104),                                # 2: 0
    probe(107),                                # 3: 0
])

# ---- actions (2.2) ----------------------------------------------------------

# ERRNO: data capped at MAX_ERRNO (4095), the call returns -data; data 0
# returns 0 with no error (:1268-1274).
trace("s_act_errno_data", [
    install(prologue([(102, [ret(ERRNO | 0)]), (104, [ret(ERRNO | 1)]), (107, [ret(ERRNO | 4095)]),
                      (108, [ret(ERRNO | 4096)]), (1000, [ret(ERRNO | 65535)])])),   # 0: 0
    probe(102),                                # 1: 0
    probe(104),                                # 2: -1
    probe(107),                                # 3: -4095
    probe(108),                                # 4: -4095 (capped)
    probe(1000),                               # 5: -4095 (capped)
])

# TRAP: the call returns its number after rt_sigreturn (syscall_rollback) and
# the handler records {nr, data, arch} (force_sig_seccomp, :1276-1281).
trace("s_act_trap_data", [
    install(prologue([(102, [ret(TRAP | 7)]), (104, [ret(TRAP | 0)])])),   # 0: 0
    probe(102),                                # 1: 102, sigsys {102, 7, X86_64}
    probe(104),                                # 2: 104, sigsys {104, 0, X86_64}
    probe(107),                                # 3: 0, sigsys null
    probe(102, args=[1, 2, 3]),                # 4: 102, sigsys {102, 7, X86_64}
])

# TRAP in a child: the child's handler runs, the child reports 102 through
# the page, and the parent sees the record.
trace("s_act_trap_child", [
    install(prologue([(102, [ret(TRAP | 9)])])),   # 0: 0
    child(102),                                # 1: child {ret 102}, sigsys {102, 9, X86_64}
    child(104),                                # 2: child {ret 0}
])

# LOG: seccomp_log with the action logged, the call proceeds (:1332-1334);
# with and without the install's log flag (the match's `log` at skip).
trace("s_act_log", [
    install(prologue([(102, [ret(LOG)])]), flags=["log"]),   # 0: 0
    probe(102),                                # 1: 0
    install(prologue([(104, [ret(LOG | 5)])])),              # 2: 0
    probe(104),                                # 3: 0
    probe(102),                                # 4: 0
])

# TRACE with no tracer: ptrace_event_enabled is false, -ENOSYS (:1283-1324).
trace("s_act_trace", [
    install(prologue([(102, [ret(TRACE)]), (104, [ret(TRACE | 5)])])),   # 0: 0
    probe(102),                                # 1: -ENOSYS
    probe(104),                                # 2: -ENOSYS
    probe(107),                                # 3: 0
])

# KILL_THREAD (:1344-1359): the mode becomes DEAD, the forced SIGSYS kills the
# single-threaded child; a second child, with the same chain, is allowed 104.
trace("s_act_kill_thread_child", [
    install(prologue([(102, [ret(KILL_THREAD)])])),   # 0: 0
    child(102),                                # 1: child {signal 31}
    child(104),                                # 2: child {ret 0}
])

# KILL_PROCESS: the same arm, the group killed (one thread).
trace("s_act_kill_process_child", [
    install(prologue([(102, [ret(KILL_PROCESS)])])),  # 0: 0
    child(102),                                # 1: child {signal 31}
])

# A non-canonical action takes the default arm, a kill (:1344).
trace("s_act_unknown_action_child", [
    install(prologue([(102, [ret(0x10000)]), (104, [ret(0x4abc0000 | 9)])])),   # 0: 0
    child(102),                                # 1: child {signal 31}
    child(104),                                # 2: child {signal 31}
])

# RET|A with A loaded from args[0]: 0 is KILL_THREAD, ALLOW allows, an ERRNO
# word is an errno, a TRAP word traps in the child.
trace("s_act_ret_a_child", [
    install(prologue([(102, [ld(arg(0)), insn(RET_A)])])),   # 0: 0
    child(102, args=[0]),                      # 1: child {signal 31}
    child(102, args=[ALLOW]),                  # 2: child {ret 0}
    child(102, args=[ERRNO | 9]),              # 3: child {ret -9}
])

trace("s_act_ret_a_trap_child", [
    install(prologue([(102, [ld(arg(0)), insn(RET_A)])])),   # 0: 0
    child(102, args=[TRAP | 1]),               # 1: child {ret 102}, sigsys {102, 1, X86_64}
])

# DIV|X: the translation's guard returns 0 for X == 0 (KILL_THREAD); with X
# non-zero A = args[0] / X.
trace("s_act_div_x_child", [
    install(prologue([
        (102, [insn(LDX_IMM, k=0), ld(arg(0)), insn(DIV_X), insn(RET_A)]),
        (104, [insn(LDX_IMM, k=2), ld(arg(0)), insn(DIV_X), insn(RET_A)]),
    ])),                                       # 0: 0
    child(102, args=[ALLOW]),                  # 1: child {signal 31} (X == 0)
    child(104, args=[2 * ALLOW]),              # 2: child {ret 0}
    child(104, args=[2 * (ERRNO | 3)]),        # 3: child {ret -3}
])

# ---- the language, driven by the arguments (self probes, safe actions) ------

# ALU with immediates: A = args[0] & 0xff after a tour that cancels out.
trace("s_lang_alu_k", [
    install(prologue([(102, [
        ld(arg(0)), insn(ADD_K, k=1), insn(SUB_K, k=1), insn(MUL_K, k=3), insn(DIV_K, k=3),
        insn(AND_K, k=0xff), insn(OR_K, k=0), insn(XOR_K, k=0), insn(LSH_K, k=4), insn(RSH_K, k=4),
        insn(NEG), insn(NEG),
        jeq(5, 0, 1), ret(ERRNO | 5), ret(ERRNO | 6)])])),   # 0: 0
    probe(102, args=[5]),                      # 1: -5
    probe(102, args=[0x105]),                  # 2: -5 (masked)
    probe(102, args=[6]),                      # 3: -6
    probe(102, args=[0x1ff]),                  # 4: -6 (0xff, not 5)
])

# ALU and jumps with X: X = args[0], A = args[1].
trace("s_lang_alu_x", [
    install(prologue([(102, [
        ld(arg(0)), insn(TAX), ld(arg(1)),
        insn(ADD_X), insn(SUB_X), insn(MUL_X), insn(OR_X), insn(AND_X), insn(XOR_X),   # A = (A*X | X) & X ^ X ... cancels to A*X&X^X
        insn(LSH_X), insn(RSH_X),
        ld(arg(1)),                            # A = args[1] again
        insn(JEQ_X, 0, 1), ret(ERRNO | 2),
        insn(JGT_X, 0, 1), ret(ERRNO | 1),
        insn(JSET_X, 0, 1), ret(ERRNO | 3),
        ret(ERRNO | 8)])])),                   # 0: 0
    probe(102, args=[5, 5]),                   # 1: -2 (A == X)
    probe(102, args=[3, 5]),                   # 2: -1 (A > X)
    probe(102, args=[4, 2]),                   # 3: -8 (2 & 4 == 0)
    probe(102, args=[6, 2]),                   # 4: -3 (2 & 6)
    probe(102, args=[0, 0]),                   # 5: -2
])

# JGE|X, the remaining X jump, with the shifts by X.
trace("s_lang_jge_x", [
    install(prologue([(102, [
        ld(arg(0)), insn(TAX), ld(arg(1)),
        insn(JGE_X, 0, 1), ret(ERRNO | 1),
        insn(LSH_X), insn(JEQ_X, 0, 1), ret(ERRNO | 2), ret(ERRNO | 3)])])),   # 0: 0
    probe(102, args=[3, 5]),                   # 1: -1 (5 >= 3)
    probe(102, args=[1, 0]),                   # 2: -3 (0 << 1 == 0 != 1)
    probe(102, args=[2, 1]),                   # 3: -3 (1 << 2 == 4 != 2)
    probe(102, args=[0, 0]),                   # 4: -1 (0 >= 0)
])

# The conditional jumps with immediates and JA.
trace("s_lang_jumps_k", [
    install(prologue([(102, [
        ld(arg(0)),
        insn(JGT_K, 0, 1, 10), ret(ERRNO | 1),
        insn(JGE_K, 0, 1, 10), ret(ERRNO | 2),
        insn(JSET_K, 0, 1, 1), ret(ERRNO | 3),
        insn(JA, k=1), ret(ERRNO | 9),
        ret(ERRNO | 8)])])),                   # 0: 0
    probe(102, args=[11]),                     # 1: -1
    probe(102, args=[10]),                     # 2: -2
    probe(102, args=[3]),                      # 3: -3
    probe(102, args=[2]),                      # 4: -8
    probe(102, args=[U32 + 1]),                # 5: -8 (the low word is 0)
])

# The sixteen memory cells, TAX/TXA and the immediate loads.
trace("s_lang_mem", [
    install(prologue([(102, [
        ld(arg(0)), insn(ST, k=0), insn(LD_IMM, k=0), insn(LD_MEM, k=0),
        insn(TAX), insn(LD_IMM, k=2), insn(STX, k=15), insn(LDX_IMM, k=7), insn(LDX_MEM, k=15),
        insn(TXA), jeq(9, 0, 1), ret(ERRNO | 1), ret(ERRNO | 2)])])),   # 0: 0
    probe(102, args=[9]),                      # 1: -1
    probe(102, args=[8]),                      # 2: -2
])

# The 64-bit arguments: the high word of args[0] and the low word of args[5].
trace("s_lang_args_high", [
    install(prologue([
        (102, [ld(arg(0, high=True)), jeq(1, 0, 1), ret(ERRNO | 1), ret(ERRNO | 2)]),
        (104, [ld(arg(5)), jeq(77, 0, 1), ret(ERRNO | 3), ret(ERRNO | 6)]),
    ])),                                       # 0: 0
    probe(102, args=[1 << 32]),                # 1: -1
    probe(102, args=[1]),                      # 2: -2
    probe(104, args=[0, 0, 0, 0, 0, 77]),      # 3: -3
    probe(104, args=[77]),                     # 4: -6
])

# The forms seccomp_is_const_allow follows at the top level (:762-836):
# AND|K, JGE|K, JGT|K and JSET|K on nr, isolating 102 and 1000 only, so every
# other number stays constant-allow; 335 is the exception and allowed.
trace("s_lang_const_forms", [
    install([ld(NR), insn(AND_K, k=U32), jeq(102, 0, 1), ret(ERRNO | 1),
             insn(JGE_K, 0, 3, 1000), insn(JGT_K, 2, 0, 1000), insn(JSET_K, 0, 1, 0x3e8),
             ret(ERRNO | 2), ret(ALLOW)]),     # 0: 0
    probe(102),                                # 1: -1
    probe(1000),                               # 2: -2
    probe(104),                                # 3: 0
    probe(335),                                # 4: -ENOSYS
])

# ---- chains (2.3): the most-restrictive rule and the cache -----------------

# The older filter kills 102, the newer allows everything: the newer's cache
# copies the older's bitmap (bitmap_copy, :881-898), so 102 runs both and the
# kill wins (ACTION_ONLY smaller, :406-434). The sentinel's target.
trace("s_chain_older_kills_child", [
    install(prologue([(102, [ret(KILL_THREAD)])])),   # 0: 0
    install(ALLOW_ALL),                        # 1: 0
    child(102),                                # 2: child {signal 31}
    child(104),                                # 3: child {ret 0}
])

# The reverse: the newer kills.
trace("s_chain_newer_kills_child", [
    install(ALLOW_ALL),                        # 0: 0
    install(prologue([(102, [ret(KILL_THREAD)])])),   # 1: 0
    child(102),                                # 2: child {signal 31}
])

# Equal actions with different data: the newest filter's result stands
# (only a strictly smaller action replaces it, :426).
trace("s_chain_tie_data", [
    install(prologue([(102, [ret(ERRNO | 1)])])),     # 0: 0
    install(prologue([(102, [ret(ERRNO | 2)])])),     # 1: 0
    probe(102),                                # 2: -2
])

# Three filters: TRAP (0x30000) beats ERRNO (0x50000) in either order; LOG
# beats ALLOW; TRACE beats LOG.
trace("s_chain_three", [
    install(prologue([(102, [ret(ERRNO | 1)]), (104, [ret(TRAP | 1)]), (107, [ret(LOG)])])),   # 0: 0
    install(prologue([(104, [ret(ERRNO | 2)]), (107, [ret(TRACE)]), (108, [ret(ERRNO | 3)])])),   # 1: 0
    install(prologue([(102, [ret(TRAP | 2)]), (107, [ret(ALLOW)])])),   # 2: 0
    probe(102),                                # 3: 102, sigsys {102, 2, X86_64} (newest TRAP over older ERRNO)
    probe(104),                                # 4: 104, sigsys {104, 1, X86_64} (older TRAP over newer ERRNO)
    probe(107),                                # 5: -ENOSYS (TRACE over LOG over ALLOW)
    probe(108),                                # 6: -3
    probe(1000),                               # 7: -ENOSYS
])

# Four 768-instruction filters: the path budget's walk over the chain
# (:921-926, 773 eBPF instructions plus 4 each, far under 32768) and a probe
# through all four programs; 104 is a cache hit through four bitmaps.
trace("s_chain_big", [
    install(long_filter(102, ERRNO | 5)),      # 0: 0
    install(long_filter(102, ERRNO | 6)),      # 1: 0
    install(long_filter(102, ERRNO | 7)),      # 2: 0
    install(long_filter(102, ERRNO | 8)),      # 3: 0
    probe(104),                                # 4: 0
    probe(102),                                # 5: -8
])

# ---- modes and privilege (2.9, 2.10) ---------------------------------------

# Strict in a child: exit (60) is allowed and leaves with its status; getuid
# is killed with SIGKILL (:1050-1077); through seccomp(2) and prctl.
trace("s_strict_child", [
    child(60, args=[7], strict="seccomp"),     # 0: child {strict_ret 0, exited 7}
    child(102, strict="prctl"),                # 1: child {strict_ret 0, signal 9}
    child(60, args=[5], strict="prctl"),       # 2: child {strict_ret 0, exited 5}
])

# Strict after a filter: seccomp_may_assign_mode refuses (-EINVAL, :437-445),
# the filter stays, the child's call proceeds under it.
trace("s_strict_after_filter_child", [
    install(prologue([(104, [ret(ERRNO | 11)])])),    # 0: 0
    child(60, args=[3], strict="seccomp"),     # 1: child {strict_ret -EINVAL, exited 3}
    child(104, strict="prctl"),                # 2: child {strict_ret -EINVAL, ret -11}
])

# The precondition (:683-685): without CAP_SYS_ADMIN an install is -EACCES
# until no-new-privs is set; the prctl argument arms (kernel/sys.c:2632-2641).
trace("s_privilege", [
    prctl("get_seccomp"),                      # 0: 0
    prctl("get_no_new_privs"),                 # 1: 0
    capdrop(),                                 # 2: 0
    install(ALLOW_ALL),                        # 3: -EACCES
    prctl("set_no_new_privs", arg2=2),         # 4: -EINVAL
    prctl("set_no_new_privs", arg2=1, arg3=1), # 5: -EINVAL
    prctl("get_no_new_privs", arg2=1),         # 6: -EINVAL
    prctl("set_no_new_privs", arg2=1),         # 7: 0
    prctl("get_no_new_privs"),                 # 8: 1
    install(ALLOW_ALL),                        # 9: 0
    prctl("get_seccomp"),                      # 10: 2
    prctl("set_no_new_privs", arg2=1),         # 11: 0 (idempotent)
    probe(102),                                # 12: 0
])

# seccomp(2)'s queries: GET_ACTION_AVAIL for the eight actions, an unknown
# one (-EOPNOTSUPP, :2053-2075), data bits included, non-zero flags
# (-EINVAL); GET_NOTIF_SIZES (:2077).
trace("s_queries", [
    query("get_action_avail", KILL_PROCESS),   # 0: 0
    query("get_action_avail", KILL_THREAD),    # 1: 0
    query("get_action_avail", TRAP),           # 2: 0
    query("get_action_avail", ERRNO),          # 3: 0
    query("get_action_avail", USER_NOTIF),     # 4: 0
    query("get_action_avail", TRACE),          # 5: 0
    query("get_action_avail", LOG),            # 6: 0
    query("get_action_avail", ALLOW),          # 7: 0
    query("get_action_avail", 0x10000),        # 8: -EOPNOTSUPP
    query("get_action_avail", ALLOW | 1),      # 9: -EOPNOTSUPP
    query("get_action_avail", ALLOW, flags=1), # 10: -EINVAL
    query("get_notif_sizes"),                  # 11: 0
    query("get_notif_sizes", flags=2),         # 12: -EINVAL
])

# The uretprobe exception (:736-754): a filter killing 335 never fires, the
# cache answers before the program, the call itself is -ENOSYS.
trace("s_uretprobe_child", [
    install(prologue([(335, [ret(KILL_THREAD)])])),   # 0: 0
    child(335),                                # 1: child {ret -ENOSYS}
    child(102),                                # 2: child {ret 0}
])

# Mixed: the harness's file operations under a filter are cache hits and the
# file table is untouched by seccomp.
trace("s_mixed_files", [
    eventfd2(),                                # 0: 8
    pipe2(),                                   # 1: 0 (fds 9, 10)
    install(prologue([(102, [ret(ERRNO | 2)])])),     # 2: 0
    write(ref(0), 8, 3),                       # 3: 8
    write(end(1, 1), 5, 1),                    # 4: 5
    read(ref(0)),                              # 5: 8
    probe(102),                                # 6: -2
    read(end(1, 0), 5),                        # 7: 5
    probe(104),                                # 8: 0
    close(ref(0)),                             # 9: 0
    close(end(1, 1)),                          # 10: 0
    read(end(1, 0), 5),                        # 11: 0 (EOF)
])

# ---- the negative controls (section 7) ---------------------------------------
# Valid traces the kernel runs and the mirror must refuse at the named site
# (design 9.1); scripts/seccomp-controls.py checks the stop.

# TSYNC on a single thread is a successful no-op in the C (:490, :597); the
# mirror stops unsupported at seccomp_attach_filter's TSYNC arm.
trace("sk_tsync", [
    install(ALLOW_ALL, flags=["tsync"]),       # 0: 0 (Linux)
    prctl("get_seccomp"),                      # 1: 2
], table=CONTROL_TRACES)

# NEW_LISTENER returns the listener descriptor (8, the first free one); the
# mirror stops at seccomp_set_mode_filter's listener arm.
trace("sk_new_listener", [
    install(ALLOW_ALL, flags=["new_listener"]),   # 0: 8 (Linux)
    probe(102),                                # 1: 0
], table=CONTROL_TRACES)

# WAIT_KILLABLE_RECV with NEW_LISTENER is accepted by the flag tests and
# stops at the same listener arm.
trace("sk_wait_killable", [
    install(ALLOW_ALL, flags=["wait_killable_recv", "new_listener"]),   # 0: 8 (Linux)
    probe(104),                                # 1: 0
], table=CONTROL_TRACES)

# USER_NOTIF with no listener: seccomp_do_user_notification answers -ENOSYS
# (:1148-1160) in the child; the mirror stops at __seccomp_filter's arm.
trace("sk_user_notif", [
    install(prologue([(102, [ret(USER_NOTIF)])])),    # 0: 0
    child(102),                                # 1: child {ret -ENOSYS} (Linux)
], table=CONTROL_TRACES)

# A CTX load of instruction_pointer (offset 8) at run time: the engine's
# unsupportedRead; Linux compares the real pointer with 0 and answers -2.
trace("sk_ip_load", [
    install(prologue([(102, [ld(IP), jeq(0, 0, 1), ret(ERRNO | 1), ret(ERRNO | 2)])])),   # 0: 0
    probe(102),                                # 1: -2 (Linux)
], table=CONTROL_TRACES)


def render(t):
    return json.dumps(validate_trace(t), indent=2) + "\n"


def check_rules():
    """The corpus's own rules: a self probe never follows a filter that may
    kill (the validator checks it too), every accepted program is at most 768
    instructions, and no trace holds more than three child probes."""
    for t in list(TRACES.values()) + list(CONTROL_TRACES.values()):
        installs = [op["filter"] for op in t["ops"] if op["op"] == "seccomp_install" and op["filter"]]
        assert not any(i[0] == RET_K and i[3] & 0xffff0000 == ERRNO and i[3] & 0xffff in RESERVED_ERRNO
                       for p in installs for i in p), t["id"]
        assert all(len(p) <= 768 for p in installs), t["id"]
        assert sum(op["op"] == "seccomp_probe" and op["where"] == "child" for op in t["ops"]) <= 3, t["id"]
        assert not any(op["op"] == "seccomp_probe" and op["where"] == "self" and any(
            filter_may_kill(p) for p in installs) for op in t["ops"]), t["id"]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--check", action="store_true", help="verify the committed files instead of writing")
    args = parser.parse_args()
    check_rules()
    for out, table in ((OUT, TRACES), (CONTROLS, CONTROL_TRACES)):
        expected = {f"{name}.json": render(t) for name, t in table.items()}
        if args.check:
            present = {p.name: p.read_text() for p in out.glob("*.json")}
            if present != expected:
                stale = sorted(set(present) ^ set(expected) | {k for k in expected if present.get(k) != expected[k]})
                raise SystemExit(f"{out.relative_to(ROOT)} differs from scripts/seccomp-corpus.py: {stale}")
            print(f"{out.relative_to(ROOT)}: {len(expected)} traces up to date")
            continue
        out.mkdir(parents=True, exist_ok=True)
        for stale in set(p.name for p in out.glob("*.json")) - set(expected):
            (out / stale).unlink()
        for name, text in expected.items():
            (out / name).write_text(text)
        print(f"wrote {len(expected)} traces to {out.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
