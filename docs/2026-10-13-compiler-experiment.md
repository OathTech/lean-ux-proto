# The compiler experiment: witness-location stability across two optimisation levels

> Units and a correction [AGENT, 2026-10-14, after the pre-release review §9]:
> this document counts decision *outcomes* (2764, of which 1465 carry a span)
> and comparison *sites* (320). The integration record of 2026-10-13
> (`f45bde8`) wrote "969 of 1382 decisions" where the unit is outcomes. The
> result is stability of where the instrumentation lands across two builds of
> the same GCC; it is compiler evidence, not evidence about the C's semantics.

[AGENT, fork of the coordinator, 2026-10-13] under the user's direction of
2026-10-13 (fidelity, audits and census gaps while the proof campaign runs).
A measurement, not a change: the oracle, the mirror, the harness and the
evaluator are untouched. The one code change is a minimal extension of the
scratch-build mechanism (section 1).

## 1. The scratch build

Only GCC 13.3.0 is on the box, so the variable is the optimisation level.

| | oracle s2 | scratch `kernel-net-choice-os` |
| --- | --- | --- |
| identity | `cea1e9a3a5e2a55782008594d9ff5e9bc7bcfe5348258ac92bf07f87e1875295` | `c13a92db8117e7a2148178f41e3e7c5a25ae1458291f8bf03bfe5f7154552fb8` |
| `CONFIG_CC_OPTIMIZE_FOR_PERFORMANCE` | y | not set |
| `CONFIG_CC_OPTIMIZE_FOR_SIZE` | not set | y |
| every other line of `.config` | identical | identical |

`scripts/build-kernel` gained `LEANUX_KERNEL_EXTRA_DISABLE`, the mirror of
`LEANUX_KERNEL_EXTRA_ENABLE`: the two optimisation options are one Kconfig
choice, and enabling the second while the first stays set makes kconfig
discard both for the default. Each named option must resolve to not set or
the build fails; either variable makes the build a scratch build (the
`.leanux-scratch` marker names both lists, no config record is written, the
identity check refuses it unless `LEANUX_KERNEL_IDENTITY` names it).

Build: `LEANUX_KERNEL_PROFILE=net-choice LEANUX_KERNEL_EXTRA_ENABLE=CC_OPTIMIZE_FOR_SIZE
LEANUX_KERNEL_EXTRA_DISABLE=CC_OPTIMIZE_FOR_PERFORMANCE LEANUX_KERNEL_BUILD=<worktree>/.artifacts/kernel-net-choice-os
capped -m 64G -- scripts/in-bundle scripts/build-kernel` (12 jobs, about ten minutes).

## 2. What refused the image, in the order met

No per-trace check could be run. Three layers of the correspondence are
bound to the -O2 image, and each refuses the -Os image fail-closed before
any decision is compared.

| layer | rule | at -Os |
| --- | --- | --- |
| the function list (`evaluator/coverage.py`, `instrumented_lines`) | every listed function must be a symbol (or a `.part`/`.isra`/`.constprop` split of one) and own a point in an anchored file | `seccomp_set_mode_filter` has no symbol: its 30 source lines sit under `do_seccomp`; `__sys_recvfrom` and `__sys_sendto` keep their symbols but own no anchored point (their only anchored lines were `include/linux/file.h` inlines, out-of-line calls now) |
| the shared exits (`check.py`, startup) | each declared frame chain names exactly one instrumentation point | 6 of 7 chains name none (table in section 3.4) |
| the harness fixture (`harness/linux.py`, `EXPECTED_MAX_USER_WATCHES`) | the boot's `max_user_watches` must equal 53092 | 53537: the limit is derived from the RAM the kernel leaves free, and the -Os image is smaller |

The third refusal is the harness's, met when the suites were run Linux-only
(section 4): every boot fails at the fixture row, so not one observation of
the -Os kernel exists. The classification below is therefore static, from
the two images' disassembly and DWARF through the evaluator's own
`instrumented_lines` and `witness_table`, with the -Os function set extended
by the decision functions that are out-of-line there (section 3.1). The
dynamic questions, operand order and value, remain unmeasured.

## 3. Static classification

### 3.1 The function set

`correspondence/kcov.json` lists 226 functions. They are the symbols of the
-O2 image whose bodies the checker disassembles; the functions inlined into
them are reached through DWARF frames and are not listed. The list, and
every table in this section, is build-bound: it describes the -O2 image's
symbols, and a second build gets its own.

| | count | names |
| --- | --- | --- |
| listed, no symbol at -Os | 1 | `seccomp_set_mode_filter` |
| listed, symbol but no anchored point at -Os | 2 | `__sys_recvfrom`, `__sys_sendto` |
| decision-owning, inlined at -O2, out-of-line symbol at -Os (would have to be listed) | 28 | `__anon_inode_getfile`, `__bpf_prog_release`, `__clear_close_on_exec`, `__fget_files_rcu`, `__fget_light`, `__file_update_time`, `__put_unused_fd`, `__set_open_fd`, `alloc_path_pseudo`, `bpf_release_orig_filter`, `do_seccomp`, `ep_events_available`, `ep_set_busy_poll_napi_id`, `ep_timeout_to_timespec`, `ep_unregister_pollwait`, `epi_fget`, `eventfd_ctx_do_read`, `eventfd_free_ctx`, `file_free`, `free_ephead`, `inode_update_time`, `message_decrypt`, `mix_precomputed_dh`, `mod_peer_timer`, `put_pipe_info`, `sig_handler_ignored`, `swap_endian`, `wants_signal` |
| decision-owning, inlined at -O2, neither a symbol nor an anchored-point owner at -Os | 19 | `ep_remove_wait_queue`, `fdput_pos`, `file_end_write`, `file_start_write`, `get_file`, `has_duplicate_listener`, `seccomp_assign_mode`, `seccomp_attach_filter`, `seccomp_cache_prepare_bitmap`, `seccomp_filter_free`, `seccomp_get_action_avail`, `seccomp_get_notif_sizes`, `seccomp_is_const_allow`, `seccomp_prepare_filter`, `seccomp_prepare_user_filter`, `seccomp_set_mode_strict`, `seccomp_uprobe_exception`, `timespec64_equal`, `wg_cpumask_choose_online` |

The 19 are inlined into other functions at -Os (the seccomp helpers into
`do_seccomp`, the `fs.h` helpers into their callers) and their points are
reached through frames once those callers are in the set; the measurement
treats them so. 251 functions were scanned at -Os against 226 at -O2.

### 3.2 Instrumentation points by file

Lines owning a KCOV point in the scanned functions' bodies: 2614 at -O2,
2532 at -Os (2297 before the 28 out-of-line functions of 3.1 are added to
the scan). Headers lose most, since at -Os their helpers are calls.

| file | -O2 | -Os | only -O2 | only -Os |
| --- | --- | --- | --- | --- |
| include/linux/fs.h | 42 | 25 | 19 | 2 |
| include/linux/file.h | 8 | 4 | 5 | 1 |
| drivers/net/wireguard/queueing.h | 25 | 14 | 11 | 0 |
| kernel/signal.c | 130 | 119 | 17 | 6 |
| fs/eventpoll.c | 357 | 352 | 24 | 19 |
| fs/file.c | 126 | 123 | 13 | 10 |
| fs/pipe.c | 203 | 199 | 13 | 9 |
| fs/inode.c | 65 | 59 | 10 | 4 |
| net/core/filter.c | 158 | 152 | 10 | 4 |
| drivers/net/wireguard/noise.c | 111 | 109 | 11 | 9 |
| kernel/seccomp.c | 182 | 180 | 8 | 6 |
| drivers/net/wireguard/allowedips.c | 90 | 91 | 8 | 9 |
| the other 29 anchored files | 1117 | 1105 | 59 | 47 |

### 3.3 Witnesses

1382 decisions, 2764 outcomes. 1299 outcomes have an empty span by
declaration (unobservable, the user's decision of 2026-09-30). Of the
1465 with a span:

| witnessed | count |
| --- | --- |
| at -O2 and -Os | 969 |
| at -O2 only (lost at -Os) | 12 |
| at -Os only (gained) | 32 |
| at neither | 452 |

Lost at -Os (the witness line is a merged or inlined block at -Os):
`alloc_file_clone.ok=1`, `bpf_prepare_filter.check_classic_err=1`,
`bpf_prog_store_orig_filter.filter_nomem=0`, `eventfd_ctx_put.kref_put_released=1`,
`fdput_pos.pos_unlock=1`, `file_end_write.not_regular=0`, `file_start_write.not_regular=0`,
`filp_flush.file_count_zero=1`, `get_allowedips.put_cidr_failed=0`,
`seccomp_is_const_allow.case_ja=1`, `wg_cpumask_choose_online.cpu_invalid=0`,
`wg_noise_handshake_consume_initiation.ss_failed=0`.

Gained at -Os (unwitnessable at -O2 because the compiler merged the arm's
block, separate at -Os): 32, among them `__do_sys_epoll_ctl.copy_fault=1`,
`ep_insert.pwake=1`, `ep_modify.pwake=1`, `ep_poll.timed_out=1`,
`eventfd_poll.room=1`, `pipe_read.short_copy=1`, `rw_verify_area.negative_count=1`,
`vfs_read.access_not_ok=1`, `vfs_write.access_not_ok=1`,
`wg_get_device_dump.done=0/1`, `wg_receive_handshake_packet.initiation=1`,
the four `wg_noise_handshake_*` failure arms, `send4.reset_a=1`,
`seccomp_set_mode_filter.new_listener_out=1`. These are declarations that are
right against the C and whose "outcome not witnessed" status at -O2 is the
compiler's, which the census should say.

By file, the witnessed count moves by at most 6 (fs/eventpoll.c, 106 to 112);
no file loses more than 2.

### 3.4 Comparison sites and shared exits

320 declared comparisons. A cmp hook (`__sanitizer_cov_trace_*cmp*`) is on
the declared line at both levels for 311; at -O2 only for 6; at neither for
3, which are the three arms of `do_epoll_ctl`'s `switch (op)` at
fs/eventpoll.c:2580, where the scan attributes the jump table's compare to
another line (the claim point records them, so this is the scan's limit,
not a missing hook).

Folded or moved at -Os (-O2 only): `bpf_convert_filter.emit_jf_zero.target_over_len`
(filter.c:757), `get_file.prior_zero` (fs.h:1125), `keep_key_fresh.birthdate_expired`
(send.c:133), `keep_key_fresh.rx_birthdate_expired` (receive.c:231),
`timespec64_equal.nsec` and `.sec` (time64.h:49).

Shared exits (build-bound declarations: each names a frame chain of the
-O2 image): of the seven declared frame chains, only `ep_modify`'s
(`fs/eventpoll.c:1979 < :2604`) exists at -Os. `file_end_write`,
`__file_update_time`, `bpf_migrate_filter`, `seccomp_get_notif_sizes`,
`fdput` and `ep_register_epitem` name no point: the merged return blocks
they describe are -O2's.

## 4. The observation level

The six corpus suites' unsteered traces (327: handwritten 41, critic 32,
wireguard 128, pipes 23, epoll 43, seccomp 60) were run Linux-only through
`harness.linux` on both kernels, and twice on s2.

| run | traces with observations | chunk failures |
| --- | --- | --- |
| -Os | 0 | 32 at the fixture row (`max_user_watches` 53537, not 53092); 3 seccomp chunks over the 16 MiB console limit (this driver's chunking) |
| s2 | 307 | the same 3 seccomp chunks |
| s2, second run | 307 | the same 3 |
| s2 against s2 | 307 traces, 1228 operations, 0 differing fields | |

So the "nothing changes with -Os" claim is neither confirmed nor refuted at
the observation level; the only observable that differed is the fixture
value itself, which is not WireGuard's or epoll's behaviour but the memory
the image leaves. The s2-against-s2 baseline shows the Linux-only
observations are exact run to run, so a comparison would have been clean
had the harness accepted the boot.

## 5. Classification

| class | what | count |
| --- | --- | --- |
| (1) compiler-bound, structural | the function list's membership (1 + 2 + 47 names); six shared-exit chains; the fixture constant | 56 names, 6 chains, 1 constant |
| (1) compiler-bound, per declaration | witnesses lost at -Os; comparison hooks folded at -Os | 12 outcomes, 6 sites |
| (1) in the other direction | outcomes unwitnessable at -O2 by a merged block, witnessable at -Os | 32 outcomes |
| (2) wrong against the C regardless | none established; the static evidence found no declaration that fails at both levels for a reason the C explains | 0 |
| (3) observation disagreement | not measurable (no -Os observation obtainable) | — |

What survives both levels, 969 witnessed outcomes and 311 comparison sites,
is witness-location stability: the declared lines own a hook in both images
of the same GCC 13.3.0. That is evidence about where the instrumentation
lands, not about the C's semantics; the C-source reasoning for a declaration
is the audit and the design document that declared it, and no dynamic
evidence (operand order and value at the 311 sites, the outcomes taken)
was obtained at -Os, since no observation of that image exists.

## 6. Recommendation

The dependence on the compiler is mostly structural, not per declaration, so
a `compiler_bound` mark on individual declarations would mislabel it. Three
changes, each small, would make a second build runnable and the dependence
explicit:

1. `kcov.json` carries a `build` stanza (GCC version, the optimisation
   option, the identity it was settled against), and the `functions` list is
   documented as that build's symbols. A second build gets a second table or
   a documented delta; there is no build-independent function list.
2. `evaluator/coverage.py` resolves a listed function with no symbol through
   the DWARF inlined-subroutine ranges inside the listed symbols that contain
   it, instead of refusing the image. That one change would have let the
   per-trace run proceed here, and it is the same mechanism that already
   names inlined callees from frames.
3. The harness's fixture constants (`EXPECTED_MAX_USER_WATCHES` today) are
   recorded per kernel identity in the identity file rather than as one
   number, since they are properties of the image.

For the simulation proof the useful statement is narrower than a semantic
one: the 969 outcomes and 311 sites are where two optimisation levels of one
compiler agree on the witness location, a property of the builds that says
nothing by itself about the C; the 12 + 6 + 32 outcomes and the six shared
exits are where the correspondence's witness is demonstrably build-bound,
so a proof must rely on the C alone there, and it should rely on the C
rather than the witness everywhere else too. Two dynamic builds would test
more implementations; they would not upgrade the correspondence to a
simulation theorem.

## 7. Reproduction and leftovers

Static diff: `.artifacts/static-diff.py` in the worktree (reads both images
with the evaluator's `instrumented_lines` and `witness_table`, scans
`objdump -dl` for cmp hooks), output `.artifacts/static-diff.json`.
Linux-only runs: `.artifacts/linux-only.py` and `run-linux-only.sh`. All
ephemeral. The scratch kernel `.worktrees/compiler-exp/.artifacts/kernel-net-choice-os`
is deleted with this report; rebuild it with the command in section 1.
