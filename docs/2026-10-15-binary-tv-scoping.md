# Binary translation validation: scope and executable probe

**Go for a bounded checker-development phase; no-go for claiming WireGuard
simulation under unmodified Kraken.** A standalone index-hashtable lookup
runs from entry through return under Kraken and agrees three ways with the
mirror and the recorded oracle operation. The remaining work is substantial:
instruction extensions, byte-to-semantics binding, state relations, call
contracts and a checker soundness theorem. This is evidence of feasibility,
not a simulation proof or a full-function certificate.

Report written 2026-10-14, under the charter's requested filename.
[USER, 2026-10-14] WireGuard-only scoping, three-day budget, the pinned oracle
and Kraken, an isolated v4.35.0 package, no merge or push.
[AGENT, scoping, 2026-10-14] Choose the index lookup's same-bucket miss after
finding `bsr` on the allowed-IPs lookup's nonempty path; use explicit hook
and environment contracts, with no instruction substitutions. The first
three-question checkpoint reported no-go for the full unmodified instruction
set and go for this restricted probe. No change to the project's proof gate
is proposed or made here.

[AGENT, scoping, 2026-10-14] Keep Kraken opt-in to `binary/`, including its
source-lock consumer. Its source pin is checked by the probe; ordinary
archive-bundle staging and verification explicitly identify it as outside
their scope. This prevents the new Git pin from breaking those commands.

| Pin | Value |
| --- | --- |
| Mirror baseline | `df3bbcab11b72a406b3097764928fa3fac97682f` |
| Mirror edit | Only `fromPeers : List PeerId` in `WG/NetlinkDump.lean` |
| Kraken | `8af78062037bc237b341d20252aafd1797c1bcb7` |
| Probe toolchain | `leanprover/lean4:v4.35.0`; root remains v4.33.1 |
| Oracle identity | `6b2018b99f086345ce9fa316a89c76d27b40b536d5feb4402510e5fb62a5ae24` |
| Oracle ELF SHA256 | `16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774` |
| Reproduce concrete comparison | `capped -- python3 binary/run.py` from the task worktree |
| Reproduce census | `capped -- python3 binary/census.py` after building the probe |
| Reproduce symbolic/axiom checks | In `binary/`: `capped -- lake env lean Symbolic.lean` and `capped -- lake env lean Axioms.lean` |

## Ranked blockers and scope of the recommendation

| Rank | Finding | Consequence / resolution |
| ---: | --- | --- |
| 1 | No binding theorem from the ELF bytes to Kraken's assembly AST. Kraken explicitly accepts some unencodable assembly. The probe trusts binutils, checks relative branch displacements, and supplies actual instruction lengths and PCs. | A certificate checker must validate decoding or explicitly trust a decoder. `fakeLayout` cannot be used. Also establish which boot/runtime text patches can affect each certified range. The image hash alone does not establish runtime byte identity. |
| 2 | Instruction gaps: 150 of 12,340 instructions fail the parser, over 49 of 102 symbol bodies. | Mostly small extensions, but they need reviewed semantics and tests, especially flags, `rep stos`, atomic operations and zero-input `bsr`. Parser acceptance alone is not validation of a semantic implementation. |
| 3 | DWARF supplies layouts, not ownership, lifetimes, aliasing, frame invariants or loop invariants. Hook/environment summaries remain assumptions. | Generate representation equations, then prove that entry relations and calls preserve them. The relational and compositional work is likely larger than the opcode work. |
| 4 | KCOV is a first-occurrence projection, and there is no one-to-one equality between decisions and coverage points. | For repeated visits the present trace cannot check a full sequence. Certificates need explicit many-to-many match points, stuttering and loop invariants. No claim that per-block checking eliminates invariant discovery. |
| 5 | Default `bv_decide` adds native-verification axioms on these goals. | Preserve the existing gate; either avoid native reflection, replay certificates in the kernel, or explicitly approve a separate trust policy. The small symbolic probe needs no extra axiom. |
| 6 | The probe covers one miss and no successful reference acquisition. | Extend to successful and collision-chain cases before treating even the index lookup as validated on its whole domain. |

The shape resembles [Sewell, Myreen and Klein's translation-validation work](https://trustworthy.systems/publications/nictaabstracts/Sewell_MK_13.abstract),
but its result cannot be borrowed for this checker. In particular, an
untrusted producer of decision certificates still needs a sound validator;
DWARF and compiler witnesses cannot stand in for that theorem.

## 1. Toolchain and axioms

The isolated package builds the executable and imports both Kraken's parser
and semantics and the mirror runner. Its path dependencies are `..` and
`../.deps/kraken`. The latter is a private archive of the exact Git commit,
verified against the read-only shared clone by `binary/run.py`; no shared
dependency build output is used or changed. Lake actually writes dependency
outputs under each dependency's `.lake`, not all under `binary/.lake` as the
charter anticipated. All three directories are private to this worktree.

The initial combined `lake build binary-probe Kraken Leanux` **failed**:
`Kraken.X64.PrintATTTests` and `Kraken.AArch64.PrintTests` read test fixtures
relative to the package invocation directory. Building `Kraken` from the
private dependency directory with `lake +leanprover/lean4:v4.35.0 build Kraken`
passes (41 jobs); the probe and mirror build passes separately. The upstream
`Kraken.X64.Examples.IncrementDMA` has a `sorry` warning at line 70. It is
outside the probe's import closure; building a library glob does not make
every example a dependency of the runner. `Kraken/Eval.lean` also defines an
`unsafe` meta elaborator; it is not used to prove the symbolic result.

| Experiment in `binary/Axioms.lean` | Observed axioms |
| --- | --- |
| XOR cancellation at widths 8, 32, 64 with `bv_decide` | Standard three plus respectively `width8._native.bv_decide.ax_1_5`, `width32._native.bv_decide.ax_1_5`, `width64._native.bv_decide.ax_1_5` |
| Concrete 8-bit equality with `decide` | None |
| 8-bit equality / `toNat` correspondence | None |
| `Operation.interp`, `Executable.step` | `propext`, `Classical.choice`, `Quot.sound` |
| Actual CMP and CMP/JE region proofs in `Symbolic.lean` | Standard three only |

The extra axioms have type
`Std.Tactic.BVDecide.Reflect.verifyBVExpr <expression> <certificate> = true`.
In this toolchain they are fresh axioms generated by
`Lean/Meta/Native.lean:nativeEqTrue`, not a dependency named
`Lean.ofReduceBool`. Initial addition/subtraction tests simplified without
native reflection; XOR tests were used to expose the actual trust cost.
A future gate must examine transitive axioms, not just blacklist older names.

`decide` works for concrete checks but enumerating two arbitrary 64-bit words
is not a feasible universal proof. `omega` handles bounded integer arithmetic
and equalities after `toNat` conversion; it does not replace a bitblaster for
arbitrary masks, rotates and multiplication. Ordinary BitVec lemmas suffice
for the probe's subtraction/zero-test equivalence. No proof-gate change is
needed for that route. The small examples are experiments requested by the
charter, not additions to the registered proof campaign.

## 2. Instruction and addressing coverage

`binary/census.py` disassembles the whole image, selects the symbols named in
`kcov.json` including compiler suffixes, bounds each by ELF symbol size,
resolves **every instruction** with `addr2line -i`, and retains every selected
symbol with a WireGuard frame. Thus inline helpers, including header code,
are counted in their containing body once; they are not counted again as
separate functions. Branch-free helpers inside these ranges are included.
The full ELF includes unrelated symbols; this census is the anchored
WireGuard set, not a transitive disassembly of every service it calls.

Each instruction's complete operand spelling goes through the actual Kraken
parser. Presentation normalization strips objdump comments/symbol annotations
and replaces direct target addresses with labels. It neither drops prefixes
nor replaces instructions. Unsupported forms are retained with their parser
error. Symbol padding is excluded: an early census including padding counted
12,515 instructions and is superseded by the sized-symbol result below.

| Measurement | Count |
| --- | ---: |
| Anchored WireGuard symbol bodies | 102 |
| Instructions, including inline code | 12,340 |
| Parser-supported instructions with implemented constructors | 12,190 |
| Unsupported, shallow (local ISA/parser work) | 150 |
| Unsupported, deep (`gs`, MSRs, interrupt state) | 0 |
| Bodies with no parser failures | 53 |
| Instructions attributed to an inline chain | 6,150 |
| RIP-relative operands | 194 |
| Indirect calls, with AST/interpreter support but rejected GNU `*` spelling | 5 |

“Supported” is a parser/implementation census, not an instruction-correctness
proof. Address forms with register base, displacement and scaled index work;
three index-only LEAs fail because the parser expects a base register. Five
indirect calls fail at GNU's `*`, despite `RelRegOrMem.reg/mem` and the call
interpreter already existing. RIP-relative loads, stores and LEAs already
use the real next PC in `AddrExpr.interp`; they need mapped data and a real
layout, not a new addressing semantics.

| Unsupported form | Count | Work needed |
| --- | ---: | --- |
| `js`, `jge`, `jg`, `jns`, `setg` | 75 | Add missing signed/status conditions; SF/OF already exist |
| `rep stos %rax,%es:(%rdi)` | 22 | Counted stores, RCX/RDI and DF; state the long-mode ES and DF premises |
| `xadd`, `cmpxchg`, `xchg` | 22 | Read-modify-write semantics and flags; single CPU does not justify ignoring arbitrary interruptions |
| `ud2` | 11 | Explicit exceptional exit, not a no-op; prove unreachable on admitted paths or model failure |
| Indirect `call *...` | 5 | Parser spelling |
| `bsr` | 4 | Bit scan and zero-input destination/flag policy |
| `div` | 3 | Quotient/remainder and overflow/divide-by-zero behavior |
| Index-only `lea` | 3 | Parser addressing form |
| `bt`, `bts` | 3 | Bit indexing, memory form where applicable, CF |
| `cltq` | 2 | Sign-extension alias |

No `lock`, `endbr64`, `%gs`, `swapgs`, `cli`, `sti`, `pushf`, `popf`, MSR
instruction or indirect jump occurs in this anchored set. In this UP build,
`pcpu_hot` is an ordinary data symbol: 46 references to `pcpu_hot+8` are to
the preempt count, and three to `pcpu_hot` read `current_task`. Per-CPU caches
inside out-of-line allocation services are outside this census. For a build
that does use `%gs`, a constant CPU-0 base is a reasonable sequential
extension, but its actual boot-time value and stability must be premises;
one CPU does not by itself make `swapgs`, faults or interrupts disappear.

Allowed-IPs `lookup` itself has 103 supported instructions, but its
`common_bits` callee has three unsupported `bsr` instructions. Linux's
`arch/x86/include/asm/bitops.h:367–420` explicitly relies on retaining the
destination for a zero source. This is a CPU-semantics choice to settle,
not simply a spelling fix; the zero case cannot be represented as an
arbitrary destination if the desired proof needs the retained value.
[LLVM's own subtarget description](https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/X86/X86Subtarget.h)
also distinguishes zero-input destination preservation from implicit
32-to-64-bit zero extension. `counter_validate` has no standalone symbol:
79 instructions attributed to its inline frame occur in `wg_packet_rx_poll`.

### Per-function census

KCOV transfers include direct calls and tail jumps to `trace_pc`. “First
blocker” means the lowest-address unsupported instruction, not necessarily
the first reached on any particular path. Every row is regenerable with the
census command above; raw listings and JSON stay ephemeral.

| Function (splits separate) | Instructions | Supported | Shallow | Deep | KCOV transfers | First blocker |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `kdf.constprop.0` | 114 | 114 | 0 | 0 | 7 | — |
| `message_ephemeral` | 41 | 41 | 0 | 0 | 3 | — |
| `mix_dh` | 57 | 57 | 0 | 0 | 3 | — |
| `wg_noise_precompute_static_static` | 46 | 46 | 0 | 0 | 4 | — |
| `wg_noise_handshake_init` | 56 | 55 | 1 | 0 | 3 | `ffffffff813965f5: rep stos %rax,%es:(%rdi)` |
| `wg_noise_handshake_clear` | 18 | 18 | 0 | 0 | 1 | — |
| `wg_noise_keypair_put` | 57 | 56 | 1 | 0 | 9 | `ffffffff8139670b: xadd   %ebp,0x498(%rbx)` |
| `wg_noise_keypair_get` | 76 | 73 | 3 | 0 | 12 | `ffffffff813967fa: cmpxchg %r12d,0x0(%r13)` |
| `wg_noise_keypairs_clear` | 20 | 20 | 0 | 0 | 1 | — |
| `wg_noise_expire_current_peer_keypairs` | 42 | 42 | 0 | 0 | 5 | — |
| `wg_noise_received_with_keypair` | 39 | 39 | 0 | 0 | 5 | — |
| `wg_noise_set_static_identity_private_key` | 57 | 57 | 0 | 0 | 4 | — |
| `wg_noise_handshake_create_initiation` | 190 | 190 | 0 | 0 | 7 | — |
| `wg_noise_handshake_consume_initiation` | 321 | 318 | 3 | 0 | 15 | `ffffffff8139712f: rep stos %rax,%es:(%rdi)` |
| `wg_noise_handshake_create_response` | 166 | 166 | 0 | 0 | 7 | — |
| `wg_noise_handshake_consume_response` | 313 | 311 | 2 | 0 | 11 | `ffffffff81397bcb: rep stos %rax,%es:(%rdi)` |
| `wg_noise_handshake_begin_session` | 176 | 175 | 1 | 0 | 16 | `ffffffff8139800f: xadd   %rax,0xc43e29(%rip)` |
| `wg_newlink` | 177 | 172 | 5 | 0 | 21 | `ffffffff813983fd: js L_ffffffff8139854d` |
| `wg_destruct` | 67 | 66 | 1 | 0 | 1 | `ffffffff813986c6: rep stos %rax,%es:(%rdi)` |
| `wg_stop` | 134 | 129 | 5 | 0 | 15 | `ffffffff813988d4: jge L_ffffffff813989a1` |
| `wg_open` | 71 | 70 | 1 | 0 | 10 | `ffffffff81398ac2: js L_ffffffff81398b2e` |
| `wg_netns_pre_exit` | 55 | 55 | 0 | 0 | 7 | — |
| `wg_xmit` | 309 | 308 | 1 | 0 | 41 | `ffffffff81398d8d: call   *0x20(%rax)` |
| `peer_remove_after_dead` | 75 | 73 | 2 | 0 | 9 | `ffffffff81399337: xadd   %ebp,0x420(%rbx)` |
| `wg_peer_create` | 114 | 113 | 1 | 0 | 6 | `ffffffff8139948a: xadd   %rax,0xc429b6(%rip)` |
| `wg_peer_get_maybe_zero` | 76 | 73 | 3 | 0 | 12 | `ffffffff8139965a: cmpxchg %r12d,0x0(%r13)` |
| `wg_peer_remove` | 28 | 28 | 0 | 0 | 3 | — |
| `wg_peer_remove_all` | 77 | 77 | 0 | 0 | 5 | — |
| `wg_peer_put` | 44 | 43 | 1 | 0 | 7 | `ffffffff81399912: xadd   %ebp,0x420(%rbx)` |
| `wg_queued_expired_zero_key_material` | 13 | 13 | 0 | 0 | 1 | — |
| `wg_expired_send_persistent_keepalive` | 17 | 17 | 0 | 0 | 3 | — |
| `wg_expired_new_handshake` | 10 | 10 | 0 | 0 | 1 | — |
| `wg_expired_retransmit_handshake` | 71 | 71 | 0 | 0 | 9 | — |
| `wg_expired_zero_key_material` | 68 | 65 | 3 | 0 | 9 | `ffffffff81399be3: xadd   %ebp,0x68(%rbx)` |
| `wg_expired_send_keepalive` | 52 | 52 | 0 | 0 | 7 | — |
| `wg_timers_data_sent` | 63 | 63 | 0 | 0 | 9 | — |
| `wg_timers_data_received` | 62 | 62 | 0 | 0 | 9 | — |
| `wg_timers_handshake_initiated` | 53 | 53 | 0 | 0 | 6 | — |
| `wg_timers_handshake_complete` | 10 | 10 | 0 | 0 | 1 | — |
| `wg_timers_session_derived` | 40 | 40 | 0 | 0 | 4 | — |
| `wg_timers_any_authenticated_packet_traversal` | 56 | 56 | 0 | 0 | 7 | — |
| `wg_prev_queue_dequeue` | 53 | 52 | 1 | 0 | 9 | `ffffffff8139a831: xchg   %rax,(%rbx)` |
| `wg_packet_send_handshake_initiation` | 68 | 67 | 1 | 0 | 5 | `ffffffff8139a8c5: rep stos %rax,%es:(%rdi)` |
| `encrypt_packet` | 212 | 209 | 3 | 0 | 19 | `ffffffff8139a9dd: rep stos %rax,%es:(%rdi)` |
| `wg_packet_handshake_send_worker` | 9 | 9 | 0 | 0 | 1 | — |
| `wg_packet_send_queued_handshake_initiation` | 88 | 84 | 4 | 0 | 12 | `ffffffff8139ad79: jg L_ffffffff8139ae1d` |
| `wg_packet_send_handshake_response` | 73 | 72 | 1 | 0 | 5 | `ffffffff8139aec3: rep stos %rax,%es:(%rdi)` |
| `wg_packet_tx_worker` | 166 | 165 | 1 | 0 | 24 | `ffffffff8139b25d: jg L_ffffffff8139b193` |
| `wg_packet_encrypt_worker` | 312 | 303 | 9 | 0 | 37 | `ffffffff8139b360: jge L_ffffffff8139b740` |
| `wg_packet_purge_staged_packets` | 41 | 41 | 0 | 0 | 4 | — |
| `wg_packet_send_staged_packets` | 525 | 512 | 13 | 0 | 68 | `ffffffff8139bab5: xadd   %r12,(%rax)` |
| `wg_packet_send_keepalive` | 37 | 37 | 0 | 0 | 5 | — |
| `decrypt_packet` | 155 | 154 | 1 | 0 | 14 | `ffffffff8139c853: rep stos %rax,%es:(%rdi)` |
| `wg_packet_handshake_receive_worker` | 317 | 309 | 8 | 0 | 38 | `ffffffff8139cb17: jge L_ffffffff8139cecf` |
| `wg_packet_rx_poll` | 585 | 580 | 5 | 0 | 65 | `ffffffff8139d021: rep stos %rax,%es:(%rdi)` |
| `wg_packet_decrypt_worker` | 172 | 165 | 7 | 0 | 23 | `ffffffff8139da42: jge L_ffffffff8139dbe3` |
| `wg_packet_receive` | 692 | 682 | 10 | 0 | 92 | `ffffffff8139e142: jge L_ffffffff8139e7ec` |
| `wg_receive` | 31 | 31 | 0 | 0 | 6 | — |
| `send4` | 230 | 229 | 1 | 0 | 27 | `ffffffff8139e93b: rep stos %rax,%es:(%rdi)` |
| `send6` | 198 | 194 | 4 | 0 | 15 | `ffffffff8139ed18: rep stos %rax,%es:(%rdi)` |
| `wg_socket_send_skb_to_peer` | 66 | 66 | 0 | 0 | 8 | — |
| `wg_socket_send_buffer_to_peer` | 49 | 49 | 0 | 0 | 3 | — |
| `wg_socket_endpoint_from_skb` | 116 | 115 | 1 | 0 | 9 | `ffffffff8139f230: rep stos %rax,%es:(%rdi)` |
| `wg_socket_send_buffer_as_reply_to_skb` | 101 | 99 | 2 | 0 | 8 | `ffffffff8139f43a: rep stos %rax,%es:(%rdi)` |
| `wg_socket_set_peer_endpoint` | 173 | 173 | 0 | 0 | 21 | — |
| `wg_socket_set_peer_endpoint_from_skb` | 42 | 41 | 1 | 0 | 4 | `ffffffff8139f8c0: rep stos %rax,%es:(%rdi)` |
| `wg_socket_clear_peer_endpoint_src` | 12 | 12 | 0 | 0 | 1 | — |
| `wg_socket_reinit` | 49 | 49 | 0 | 0 | 7 | — |
| `wg_pubkey_hashtable_add` | 32 | 32 | 0 | 0 | 3 | — |
| `wg_pubkey_hashtable_remove` | 29 | 29 | 0 | 0 | 5 | — |
| `wg_pubkey_hashtable_lookup` | 49 | 49 | 0 | 0 | 7 | — |
| `wg_index_hashtable_insert` | 109 | 109 | 0 | 0 | 21 | — |
| `wg_index_hashtable_replace` | 41 | 41 | 0 | 0 | 5 | — |
| `wg_index_hashtable_remove` | 25 | 25 | 0 | 0 | 5 | — |
| `wg_index_hashtable_lookup` | 62 | 62 | 0 | 0 | 10 | — |
| `root_remove_peer_lists` | 71 | 70 | 1 | 0 | 11 | `ffffffff813a057f: rep stos %rax,%es:(%rdi)` |
| `common_bits` | 73 | 70 | 3 | 0 | 10 | `ffffffff813a07af: bsr    %edx,%eax` |
| `lookup` | 103 | 103 | 0 | 0 | 14 | — |
| `add.isra.0` | 506 | 504 | 2 | 0 | 28 | `ffffffff813a0ce9: bt     %ecx,%eax` |
| `wg_allowedips_free` | 37 | 37 | 0 | 0 | 5 | — |
| `wg_allowedips_insert_v4` | 26 | 26 | 0 | 0 | 1 | — |
| `wg_allowedips_insert_v6` | 29 | 29 | 0 | 0 | 1 | — |
| `wg_allowedips_remove_by_peer` | 120 | 119 | 1 | 0 | 17 | `ffffffff813a1435: lea    0x8(,%r15,8),%rax` |
| `wg_allowedips_read_node` | 80 | 79 | 1 | 0 | 8 | `ffffffff813a1579: lea    0x2(,%rbx,8),%ebx` |
| `wg_allowedips_lookup_dst` | 57 | 57 | 0 | 0 | 7 | — |
| `wg_allowedips_lookup_src` | 57 | 57 | 0 | 0 | 7 | — |
| `wg_ratelimiter_gc_entries` | 162 | 161 | 1 | 0 | 30 | `ffffffff813a185f: lea    0x0(,%rdx,8),%rax` |
| `wg_ratelimiter_allow` | 160 | 159 | 1 | 0 | 23 | `ffffffff813a1b71: xadd   %eax,0xc3a310(%rip)` |
| `wg_ratelimiter_init` | 108 | 107 | 1 | 0 | 12 | `ffffffff813a1e9f: bsr    %rax,%rcx` |
| `wg_ratelimiter_uninit` | 35 | 35 | 0 | 0 | 4 | — |
| `make_cookie` | 114 | 113 | 1 | 0 | 7 | `ffffffff813a209d: rep stos %rax,%es:(%rdi)` |
| `wg_cookie_checker_precompute_device_keys` | 39 | 39 | 0 | 0 | 5 | — |
| `wg_cookie_checker_precompute_peer_keys` | 15 | 15 | 0 | 0 | 1 | — |
| `wg_cookie_validate_packet` | 83 | 83 | 0 | 0 | 5 | — |
| `wg_cookie_add_mac_to_packet` | 70 | 69 | 1 | 0 | 5 | `ffffffff813a2728: jg L_ffffffff813a275a` |
| `wg_cookie_message_consume` | 84 | 84 | 0 | 0 | 7 | — |
| `wg_get_device_done` | 36 | 35 | 1 | 0 | 5 | `ffffffff813a29c7: xadd   %r12d,0x448(%rbp)` |
| `lookup_interface` | 90 | 89 | 1 | 0 | 13 | `ffffffff813a2b25: xadd   %ebp,0x448(%rbx)` |
| `wg_get_device_start` | 28 | 28 | 0 | 0 | 5 | — |
| `set_peer` | 535 | 526 | 9 | 0 | 71 | `ffffffff813a2d8c: rep stos %rax,%es:(%rdi)` |
| `wg_set_device` | 431 | 423 | 8 | 0 | 59 | `ffffffff813a3748: rep stos %rax,%es:(%rdi)` |
| `wg_get_device_dump` | 741 | 730 | 11 | 0 | 86 | `ffffffff813a3d18: js L_ffffffff813a4204` |

## 3. Globals and memory

Kraken's `DataMem = Mem 64` is already an extensible map of addresses to
bytes with reads and writes. The README's exclusion of mutable globals is
principally an assembler/loader and verification-support limitation, not a
read-only restriction in the step semantics. Unmapped access produces an
explicit effect; the probe refuses it. The stock `Effects.All` discharges
access-permission requests automatically, so a no-fault theorem needs an
additional mapping/permission invariant, not just a permission callback name.

The proposed loader initializes allocated PROGBITS data at linked virtual
addresses and zero-fills NOBITS, records permissions separately, excludes
freed init sections at post-boot entry, and overlays runtime globals and
heap structures related by R. The static image cannot supply post-boot
`current`, jiffies, cache pointers or reference counts. The certified function
must start with related **runtime** data, not freshly initialized globals.
The current image's `.data` is at `ffffffff81c00000`, size `0xd1000`; `.bss`
at `ffffffff81f8c000`, size `0x74000`. `.data..percpu` is empty in this build;
`pcpu_hot` is at `ffffffff81cc85c0`, size 64. Do not allocate a fictitious
second copy of its CPU-0 state. Section flags alone are not final kernel
page permissions (even this ELF's `.rodata` carries SHF_WRITE).

For the probe only the table, entry, output slot, stack and
`pcpu_hot.preempt_count` are mapped. That sparse provision is sufficient for
the executed miss; it is not a full-image loader. Estimate: 2–4 agent-days
for a concrete loader, relocation/runtime-patch inventory and tests; another
3–6 for its checked provisioning and frame lemmas. Optional constant-GS
support adds roughly 2–4; full interrupt/fault/VM semantics is a different
project and is not included.

## 4. Concrete three-way comparison

| Item | Result |
| --- | --- |
| Function | `wg_index_hashtable_lookup`, `ffffffff813a0470`, 208 bytes, 62 instructions |
| Corpus | `corpus/wireguard/d1_wrong_receiver_index_same_bucket.json` |
| Operation | Index 3, handshake-response injection; first three operations replayed from the coverage child's prepared hidden-input trace |
| Existing / queried index | `0x0a0b0c0d` / `0x8a0b0c0d`; same bucket, different index |
| Entry ABI | RDI table, ESI handshake mask 1, EDX query, RCX output peer slot, RSP mapped return slot |
| Machine execution | 45 body instructions, entry to actual `ret`; call instructions push real return PCs |
| Result | RAX = 0; mirror `indexLookup [.handshake] query = none` |
| Memory / ABI | All provisioned non-stack bytes unchanged, including output slot and restored preempt count; RSP advanced by 8, all callee-save registers restored |
| Coverage | Seven return PCs agree exactly in order, with no repeats on the machine path |
| Decisions | `entry=1`, `index_matches=0`, `entry=0`, `found=0`, equal both to the direct mirror call and full trace replay |
| Operands | `(0x0a0b0c0d, 0x8a0b0c0d)` at return PC `ffffffff813a04c9`, equal to the independent comparison child |
| Differential check | Pass: 1 trace, 6 operations, 20 operand pairs, 18 distinct operand rows |

Coverage PCs, in order: `ffffffff813a0489`, `ffffffff813a04a9`,
`ffffffff813a04b2`, `ffffffff813a04bc`, `ffffffff813a04d3`,
`ffffffff813a04e1`, `ffffffff813a04e8`.

No Kraken/kernel coverage or operand disagreement was observed. Two fixed
choices for Kraken's undefined values, zero and all-ones, give the same path,
registers and memory; five undefined-flag choices occur per run. This is not
a proof of independence from every undefined choice. The symbolic result
below quantifies over flags for its own region.

The machine decisions come from the successors selected by Kraken at the
build-bound branch offsets, not from copying the mirror's event array. The
certificate here is hand-written and checks one path. Unknown instructions,
PCs, accesses, calls, state shapes and mismatches fail; execution has a
1,000-step bound. `wg_peer_get_maybe_zero` is classified as a mirrored callee
but deliberately rejects if reached; there is no success-path stub returning
a convenient peer.

The runtime wrapper executes coverage/comparison calls through Kraken's
`call` and `ret`, with summaries preserving modeled data and collecting their
events. `__local_bh_enable_ip` has a conditional environment summary: balanced
512 preempt-count decrement, no pending work, preservation of represented
heap state. It is not an execution or proof of that callee's machine code.
Synthetic heap pointers instantiate R; this is not a guest-memory snapshot.
The kernel does not record its local return register or heap delta, so the
return/memory comparison is machine-versus-mirror; the independently recorded
kernel channel is coverage and comparison operands. That limit is explicit
in the probe's output.

`harness/guest.c:print_pcs` deduplicates the kernel stream in first-occurrence
order, and `harness/linux.py` requires unique PCs. Exact agreement here means
the full machine sequence equals that recorded projection on a nonrepeating
path. It cannot rule out extra repeated visits in the kernel. A general
three-way test needs nondeduplicated per-invocation PCs; no harness change was
made for this assignment.

## 5. Symbolic region

`binary/Symbolic.lean` symbolically executes the actual CMP/JE region at
`ffffffff813a04c9` (3-byte compare, 2-byte conditional jump). Kraken yields
`ZF = (EBP - R12D == 0#32)`. A BitVec subtraction lemma equates it with
`EBP.toNat == R12D.toNat`, the mirror's index comparison under R. The result
uses `Directives.interp` and `Effects.All` from OmniSemantics, arbitrary
registers and memory, and proves the selected successor. No `bv_decide`,
`sorry`, native axiom, custom axiom or unsafe proof is used.

This region begins after the comparison hook; loads establishing EBP and
R12D, the hook's frame contract and the pointer representation are premises
at its boundary, not proved by this lemma. `Sep` offers memory ownership
lemmas and can support those loads, but it is not necessary for this
register-only experiment. Neither API automatically constructs a certificate
or loop invariant. The theorem's manually specified AST still depends on the
decoder-binding work in blocker 1.

## 6. State relation

`binary/layouts.py` extracts structure size and constant member offsets from
the oracle's `peerlookup.c` and `allowedips.c` CUs, descends anonymous unions,
and rejects conflicting or nonconstant layouts. No C-header offset is used
to materialize the probe.

| Type | Size | Relevant DWARF offsets |
| --- | ---: | --- |
| `index_hashtable` | 65,536 | `hashtable=0`; zero-sized UP `lock=65536` |
| `hlist_head` | 8 | `first=0` |
| `index_hashtable_entry` | 32 | `peer=0`, `index_hash=8`, `type=24`, `index=28` |
| `hlist_node` | 16 | `next=0`, `pprev=8` |
| `allowedips_node` | 72 | `peer=0`, `bit=8`, `cidr=24`, `bit_at_a=25`, `bit_at_b=26`, `bitlen=27`, `bits=32`, `parent_bit_packed=48`, union `peer_list/rcu=56` |
| `allowedips` | 24 | `root4=0`, `root6=8`, `seq=16` |
| `pcpu_hot` | 64 | `current_task=0`, `preempt_count=8`, `cpu_number=12`, `top_of_stack=16`, `hardirq_stack_ptr=24`, `softirq_pending=32` |

Write `u_n(M,a)` for a little-endian n-byte load. Let `E` inject live entry
identities into disjoint 32-byte allocations, `P` inject live peer identities,
and `T` be the table base. For each bucket `b`, take the mirror's ordered
subsequence `L_b = filter (index % 8192 = b) indexTable`:

* `u_8(M,T+8b)` is zero for an empty subsequence, else `E(head L_b)+8`.
* For each entry e, `u_4(M,E(e)+28)=e.index`,
  `u_4(M,E(e)+24)=kindMask(e.kind)`, `u_8(M,E(e))=P(e.peer)`.
* `u_8(M,E(e)+8)` is the next entry's `E+8`, or zero;
  `u_8(M,E(e)+16)` points to the predecessor's next slot or the bucket slot.
* Integers fit their machine widths; pointers are nonzero and disjoint from
  table, stack and output. The full chain is finite and acyclic. Callee-save
  registers and return slot have the ABI relation. The preempt count is a
  balanced environment component, initialized to zero in this probe.

`materialize` constructs these equations from the replayed mirror list using
the extracted offsets. The miss does not dereference its peer pointer;
successful paths additionally require a peer/refcount relation and reference
lifetime assumptions. The preserved output slot is initialized to a sentinel
to detect an unintended write.

For the trie, add an injective node-address map, peer and child pointer
equations, `cidr ≤ bitlen ∈ {32,128}`, and the kernel's endian-swapped byte
layout. `bit_at_a/bit_at_b` implement `choose`; the bit-numbering convention
must be related to the mirror's integer arithmetic. Parent packed bits,
peer-list order, RCU union lifetime and acyclicity are invariants, not facts
inferable from DWARF. No trie execution is claimed here.

Generate offset/type/width equations and ABI field bindings from DWARF plus
a short mirror-field map. Pointer identity maps, list/trie invariants and
service footprints remain semantic inputs. Optimized locals and location
lists would need point-specific availability checks; this probe uses ABI
registers and explicit compare operands, not a general local-variable
relation generator.

## 7. Instrumentation and environment

The instruction census finds 1,317 direct `call trace_pc`, **32 tail jumps**
to `trace_pc`, 506 direct comparison calls, eight `trace_switch` calls,
and 12 direct record-hook calls (seven `kcov_timer_jiffies`, five
`kcov_dst_cache_ts`). Thus “all instrumentation is a plain call” is false:
the tail-jump cases must inherit the caller's return address. The existing
coverage evaluator already accounts for this. Other choice kinds are
recorded inside services such as allocation, randomness, timekeeping and
workqueue code; there is not a separate hook call in every anchored caller.

| Call class | Required checker contract |
| --- | --- |
| Mirrored callee | Its validated relation, stack/ABI discipline and permitted footprint; reject a missing certificate |
| Service | Explicit value/effect contract; recorded allocation/random/clock results consumed at the actual service site in order |
| Environment | Effects outside R plus any represented bookkeeping; specify allowed yields and prove represented heap preservation |
| Cut | Prove no represented-state effect, not merely an unused return value |
| Instrumentation | Coverage/comparison event semantics and preserved represented state; account for caller-save clobbers, tail calls, buffer bounds and `trace_switch` |
| Unclassified | Reject |

The proposal's “hooks return the recorded input” needs refinement: some
hooks record an identity value supplied by a caller, some write records
without returning a hidden value, and others sit inside a service wrapper.
`gen-choice-stream.py` defines those distinctions, including kinds 305–312.
Do not replace a whole service with its record writer's behavior.

An environment assumption excluding interrupts except at named yields is
not a theorem about all executions of this kernel. The future simulation
must quantify over exactly that restricted machine/environment semantics.
Single CPU alone does not justify locking, RCU, scheduler or pending-softirq
erasure. For this miss, balanced BH bookkeeping is the only represented
environment effect summarized.

## 8. Scale, estimates and next decision

| Scale measure | Count / interpretation |
| --- | --- |
| Instructions | 12,340 over 102 anchored WG bodies |
| Direct/indirect calls | 2,581 call instructions, 233 printed callee targets/forms |
| Coverage transfers | 1,349; 1,317 calls plus 32 tail jumps |
| Comparison/switch calls | 506 / 8 |
| Regions | 3,949 when splitting at branch targets and after every branch, call or return; call summaries are boundaries |
| WG-source mirror decisions | 540 of 1,406 total declarations; header-helper decisions are shared and not included in 540 |
| Index lookup | 62 instructions, 23 such regions, 10 coverage calls, 2 comparison calls, 5 mirror decision sites |

These are static counts, not path counts or proof obligations. The region
count is a reproducible upper partition for summaries, not a measured count
of successfully matched decision regions. Even the chosen function's five
decisions versus ten coverage points refutes literal density equality.
`cmov`, merged exits, multiple instructions per decision and optimized loops
require an explicit matching relation. Straight-line arithmetic is tractable;
finding and preserving the boundary invariants remains open.

Estimates below are **agent-days of work**, including debugging and review,
not elapsed parallel time. They assume a narrow sequential target and an
explicit decoder trust decision; they exclude general VM/interrupt semantics.

| Workstream | Estimate | Principal uncertainty |
| --- | ---: | --- |
| Parser/ISA extensions, loader and opcode regression cases | 8–16 | Flags, string operations, atomic/zero-input semantics and runtime text |
| Certificate producer/checker, R schema, call contracts and diagnostics | 20–40 | Optimized matches, loops, pointer footprints and correspondence extraction |
| Checker soundness theorem and composition over entries | 20–40 | All machine nondeterminism, memory framing, service assumptions, divergence/termination direction |
| First three functions after that foundation | 10–20 | Index lookup 2–4; allowed-IPs lookup plus `common_bits` 4–8; a third standalone function 4–8 |
| Total | 58–116 | Planning range, not a measured productivity result |

`counter_validate` cannot be the third standalone symbol in this image;
either certify its range inside `wg_packet_rx_poll` with an entry relation,
or choose another small standalone function. The next useful milestone is
the full index lookup over empty/miss/hit/type-reject/reference-reject paths,
with explicit contracts and one loop invariant. Fund that bounded milestone
before committing to the full WireGuard set. A proof that accepted
certificates imply simulation remains the decisive missing result.

## Validation, reproduction limits and disposition

* Combined Kraken/probe/mirror build first failed on upstream relative test
  paths; the private Kraken-root build and the separate probe/mirror build
  then passed. No upstream source was patched.
* First check invocation with `--no-build` failed freshness before any guest
  boot, because the bundle selected v4.33.1. The corrected v4.35.0 invocation
  passed the one corpus trace. No scheduling retry was used.
* Unit tests: 124 run, one skipped, pass. The full differential suite,
  controls and mutants were not run: this is an isolated scoping probe,
  not a mirror integration claim. No proof-campaign merge or gate is claimed.
* Four one-off rejection probes passed: changed return value, unmapped entry
  load, forced successful-lookup arm reaching the unimplemented peer callee,
  and reversed kernel coverage. These mutations were deleted after checking.
  The base dependency verifier passed all 680 archive/reference/source checks.
* The registered replay-window result remains lagging since `247beec` per
  `docs/proofs.md`. This assignment neither repairs nor advances that register.
* Source-lock consumers explicitly keep Kraken outside the default archive
  bundle; `binary/run.py` verifies its pinned source before building. This
  avoids making the ordinary staging/verification commands treat a Git
  checkout as a nonexistent tarball. The base mirror has no Kraken import.
* Logs, raw disassembly, layouts, prepared state and guest witnesses are
  ephemeral and are regenerated by the commands. The conclusions and code
  are the retained artifacts. Task branch only; no main update or push.

The probe deliberately does not establish successful lookup behavior,
whole-image execution, arbitrary repeats, automatic R generation, decoding
correctness, semantics correctness of every accepted opcode or a simulation
theorem. Those are named follow-on work, not failures hidden behind its pass.
