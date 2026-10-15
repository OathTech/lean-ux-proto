# Decision census and exclusion list — 2026-10-13 [AGENT, fork of the coordinator]

The "final census, and a list of exclusions with their reasons" that the
[pause-state note](2026-10-08-pause-state.md) (section 4, step 8) put after
W13, taken now that the representation batch, epoll, seccomp and review
items 7 and 8 have landed (`main` 2c7a076, oracle `kernel-net-choice-s2`,
identity `cea1e9a3…`). It updates the
[WireGuard coverage census of 2026-10-06](2026-10-06-wireguard-census.md).
Read-only: one census run on s2, the `kcov.json` configuration, the register
and the designs' out-of-scope sections. Nothing here changes the mirror,
the harness or the kernel.

A row's altitude criterion is the
[simulation-target review's](2026-10-12-simulation-target-review.md)
(section 2): a decision mirrors one C choice point with the C's operands and
in the C's order; a helper summarised as a contract (a logical lookup for a
bucket walk, a constant-outcome allocation, a lock region as one step) is a
named cut, never counted as a per-comparison mirror of what it summarises.

## 1. The census run

One run, `--decision-census --no-build` on the worktree's build of `main` 2c7a076, the
default suite list split into the four groups the claim points use, concurrent at
eight slots, oracle `kernel-net-choice-s2` (identity `cea1e9a3…` checked in every
report). The `w7-tier` suite is outside the default list and is not in this census;
its five traces were run and agreed at its landing (2c7a076).

| Group | Suites | Traces | Operations | Agreement | Operand pairs | Splits | Reruns |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A | seccomp, seccomp-generated | 260 | 1358 | 260 | 543659 | 0 | 0 |
| B | wireguard, wireguard-generated | 450 | 3147 | 450 | 40148 | 10 | 0 |
| C | handwritten, critic, generated, alloc | 1104 | 37273 | 1104 | 310482 | 0 | 0 |
| D | pipes, pipes-generated, epoll, epoll-generated | 470 | 11666 | 470 | 195173 | 0 | 0 |
| sum | | 2284 | 53444 | 2284 | 1089462 | | |

Every group `pass`. Decisions declared: 1382; outcomes 2764.

## 2. Decisions by anchored file

Every decision is `function.name`, anchored at a `file:line` of the pristine
6.12.110 source. A decision has two outcomes. An outcome is **exercised** when
at least one agreeing operation of the run took it; **unexercised** when no
operation took it although KCOV could witness it (an instrumentation point
in its span); **unobservable** when its span owns no instrumentation point
(a merged return block, a branch-free helper, a compare the compiler folded),
which the check counts without requiring a declared reason
[USER 2026-09-30].

Of the 2764 outcomes: 842 exercised, 139 unexercised and witnessable,
1219 unobservable but taken (their outcome is checked through the sibling's
witness or the operand record, not through a point of their own), 564 unobservable
and never taken. By decision: 118 with both outcomes witnessable,
745 with one (the fall-through side of an `if` without an `else` owns no line of
its own), 519 with neither (496 of them evaluated by some trace: declared
comparisons and repeatable per-instruction decisions whose check is the operand
stream, and merged blocks; the remaining 23 are listed in section 4).

| File | Decisions | Exercised | Unexercised, witnessable | Unobservable, taken | Unobservable, never taken | Functions |
| --- | --- | --- | --- | --- | --- | --- |
| `drivers/net/wireguard/allowedips.c` | 50 | 49 | 0 | 42 | 9 | 14 |
| `drivers/net/wireguard/cookie.c` | 9 | 9 | 0 | 8 | 1 | 4 |
| `drivers/net/wireguard/device.c` | 34 | 32 | 3 | 18 | 15 | 5 |
| `drivers/net/wireguard/netlink.c` | 126 | 97 | 1 | 137 | 17 | 10 |
| `drivers/net/wireguard/noise.c` | 56 | 42 | 4 | 46 | 20 | 18 |
| `drivers/net/wireguard/peer.c` | 11 | 7 | 1 | 10 | 4 | 6 |
| `drivers/net/wireguard/peerlookup.c` | 11 | 6 | 2 | 10 | 4 | 4 |
| `drivers/net/wireguard/queueing.c` | 5 | 4 | 0 | 4 | 2 | 1 |
| `drivers/net/wireguard/queueing.h` | 9 | 4 | 0 | 8 | 6 | 5 |
| `drivers/net/wireguard/ratelimiter.c` | 16 | 11 | 4 | 7 | 10 | 4 |
| `drivers/net/wireguard/receive.c` | 96 | 62 | 4 | 90 | 36 | 12 |
| `drivers/net/wireguard/send.c` | 48 | 39 | 3 | 35 | 19 | 12 |
| `drivers/net/wireguard/socket.c` | 45 | 26 | 7 | 37 | 20 | 11 |
| `drivers/net/wireguard/timers.c` | 12 | 12 | 1 | 7 | 4 | 8 |
| `fs/anon_inodes.c` | 4 | 3 | 0 | 2 | 3 | 1 |
| `fs/eventfd.c` | 24 | 17 | 3 | 21 | 7 | 7 |
| `fs/eventpoll.c` | 170 | 83 | 23 | 185 | 49 | 43 |
| `fs/fcntl.c` | 22 | 7 | 5 | 22 | 10 | 5 |
| `fs/file.c` | 57 | 43 | 9 | 41 | 21 | 19 |
| `fs/file_table.c` | 31 | 16 | 6 | 27 | 13 | 10 |
| `fs/inode.c` | 32 | 20 | 4 | 14 | 26 | 10 |
| `fs/internal.h` | 2 | 1 | 1 | 2 | 0 | 1 |
| `fs/open.c` | 8 | 3 | 2 | 6 | 5 | 2 |
| `fs/pipe.c` | 117 | 64 | 16 | 114 | 40 | 20 |
| `fs/read_write.c` | 33 | 22 | 3 | 29 | 12 | 8 |
| `include/crypto/curve25519.h` | 1 | 1 | 0 | 1 | 0 | 1 |
| `include/linux/eventpoll.h` | 3 | 2 | 0 | 2 | 2 | 2 |
| `include/linux/file.h` | 2 | 0 | 1 | 2 | 1 | 2 |
| `include/linux/fs.h` | 11 | 1 | 4 | 13 | 4 | 7 |
| `include/linux/if_vlan.h` | 1 | 0 | 1 | 1 | 0 | 1 |
| `include/linux/percpu_counter.h` | 2 | 0 | 0 | 2 | 2 | 1 |
| `include/linux/pipe_fs_i.h` | 1 | 0 | 1 | 1 | 0 | 1 |
| `include/linux/poll.h` | 2 | 2 | 0 | 1 | 1 | 2 |
| `include/linux/refcount.h` | 11 | 3 | 1 | 9 | 9 | 3 |
| `include/linux/time64.h` | 2 | 0 | 0 | 3 | 1 | 1 |
| `include/net/inet_ecn.h` | 14 | 0 | 0 | 25 | 3 | 9 |
| `include/net/ip_tunnels.h` | 2 | 3 | 0 | 1 | 0 | 1 |
| `kernel/seccomp.c` | 126 | 54 | 11 | 117 | 70 | 24 |
| `kernel/signal.c` | 59 | 31 | 10 | 35 | 42 | 15 |
| `net/core/filter.c` | 117 | 66 | 8 | 84 | 76 | 11 |
| total | 1382 | 842 | 139 | 1219 | 564 | |

## 3. Unexercised outcomes and their reasons

Each unexercised outcome is one of: **(a)** modelled but unexercised, with
the reason in the design that models it; **(b)** a declaration whose own
witness lies in a merged block or an after-loop line, witnessable in
principle, reached only together with its sibling; **(c)** a gap nobody has
written down.

The rows the census run marked **(c)** in the table below are resolved in
section 3.1; most are in fact **(a)** (structurally dead or fixture-excluded).

139 unexercised witnessable outcomes from the census run (138 after this task's
`d3_privkey_change_expires` trace): originally 90 of class (a) and 49 of class (c).
Section 3.1 resolves the 49, leaving 127 of class (a) and 11 of class (c). None of
class (b) survives, since a merged-block or after-loop witness that the sibling
reaches is counted as unobservable, not unexercised.

| Decision | Outcome | Site | Class | Reason |
| --- | --- | --- | --- | --- |
| `wg_stop.drain_handshake_ring` | true | `drivers/net/wireguard/device.c:130` | (a) | [L](2026-10-05-l-lifecycle.md) 9: down with pending work stays `unsupported` |
| `wg_xmit.gso_error` | true | `drivers/net/wireguard/device.c:181` | (a) | [W4-W7](2026-10-06-w4-w7-transmit-bulk.md) 9: `skb_gso_segment` failure: an allocation outcome, stream A |
| `wg_newlink.register_failed` | true | `drivers/net/wireguard/device.c:368` | (a) | [L](2026-10-05-l-lifecycle.md) 9: `register_netdevice` failing is A's domain, assumed success |
| `wg_get_device_dump.ret_error` | true | `drivers/net/wireguard/netlink.c:286` | (a) | [W1-W2](2026-10-06-w1-w2-netlink.md) 5: a dump failing to allocate its skb; `-EMSGSIZE` with data unreachable |
| `wg_noise_expire_current_peer_keypairs.current_keypair` | true | `drivers/net/wireguard/noise.c:193` | (c) | WireGuard paths no trace drives |
| `wg_noise_received_with_keypair.changed` | true | `drivers/net/wireguard/noise.c:269` | (c) | WireGuard paths no trace drives |
| `wg_noise_handshake_consume_response.state_changed` | true | `drivers/net/wireguard/noise.c:790` | (c) | WireGuard paths no trace drives |
| `wg_noise_handshake_begin_session.alive` | false | `drivers/net/wireguard/noise.c:843` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P5: a dead-peer arm: SMP or in-region preemption |
| `wg_peer_create.dst_cache_failed` | true | `drivers/net/wireguard/peer.c:36` | (a) | [A](2026-10-05-a-alloc.md) 10: `dst_cache_init`: lax and unsteerable, a constant-outcome decision |
| `wg_index_hashtable_insert.locked_entry` | true | `drivers/net/wireguard/peerlookup.c:145` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P7: 64 index collisions |
| `wg_index_hashtable_insert.locked_collision` | true | `drivers/net/wireguard/peerlookup.c:148` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P7: 64 index collisions |
| `wg_ratelimiter_init.table_v6_failed` | true | `drivers/net/wireguard/ratelimiter.c:185` | (a) | [L](2026-10-05-l-lifecycle.md) 9, [A](2026-10-05-a-alloc.md) 10: a creation allocation outside the model |; since B4 (2026-10-15) a constant-false decision with that reason (`kmem_cache_create` and a 16 KiB `kvcalloc` are not direct kind-305 sites: docs/2026-10-15-design-b4-load-ratelimiter.md 4.4)
| `wg_ratelimiter_gc_entries.v6_entry_iterate` | true | `drivers/net/wireguard/ratelimiter.c:70` | (a) | [E](2026-10-05-e-dos.md) 11: the periodic GC run with entries, excluded with the reason in [B4](2026-10-15-design-b4-load-ratelimiter.md) 3; **the uninit walk's arm is reached since B4** (`l_delete_ratelimited6`), the mirror having emptied the IPv4 table only before |
| `wg_ratelimiter_gc_entries.has_work` | true | `drivers/net/wireguard/ratelimiter.c:77` | (a) | [E](2026-10-05-e-dos.md) 11: as above |
| `wg_ratelimiter_gc_entries.requeue` | true | `drivers/net/wireguard/ratelimiter.c:80` | (a) | [E](2026-10-05-e-dos.md) 11: as above |
| `wg_receive_handshake_packet.wrong_packet` | true | `drivers/net/wireguard/receive.c:192` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P14: structurally dead: the worker receives handshake types only |
| `wg_packet_consume_data.epipe` | true | `drivers/net/wireguard/receive.c:528` | (c) | WireGuard paths no trace drives |
| `wg_packet_consume_data.enqueued_epipe` | false | `drivers/net/wireguard/receive.c:530` | (c) | WireGuard paths no trace drives |
| `wg_packet_receive.data` | false | `drivers/net/wireguard/receive.c:546` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P8: `prepare_skb_header` validates the type first |
| `wg_packet_tx_worker.crypted` | false | `drivers/net/wireguard/send.c:275` | (a) | [W7 tier](2026-10-13-w7-full-ring-tier.md): exercised by the `w7-tier` suite, outside the default list |
| `wg_packet_create_data.epipe` | true | `drivers/net/wireguard/send.c:322` | (a) | [W7 tier](2026-10-13-w7-full-ring-tier.md): as above |
| `wg_packet_create_data.ok_epipe` | false | `drivers/net/wireguard/send.c:326` | (a) | [W7 tier](2026-10-13-w7-full-ring-tier.md): as above |
| `send6.src_not_local` | true | `drivers/net/wireguard/socket.c:133` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: needs another local address or interface |
| `send6.reset` | true | `drivers/net/wireguard/socket.c:136` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: as above |
| `send6.route_err` | true | `drivers/net/wireguard/socket.c:141` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: as above |
| `wg_socket_send_skb_to_peer.inet6` | false | `drivers/net/wireguard/socket.c:177` | (c) | WireGuard paths no trace drives |
| `send4.src_if_mismatch` | true | `drivers/net/wireguard/socket.c:62` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: the reply must leave by a device other than the arrival one |
| `send4.reset_b` | true | `drivers/net/wireguard/socket.c:68` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: as above |
| `send4.put_rt` | true | `drivers/net/wireguard/socket.c:70` | (a) | [W8-W9](2026-10-06-w8-w9-netns-routing.md) 8: as above |
| `wg_expired_zero_key_material.already_queued` | true | `drivers/net/wireguard/timers.c:112` | (a) | [D3](2026-10-05-d3-timers.md) 9: a fire while the work is pending: scheduling |
| `eventfd_read.o_nonblock` | false | `fs/eventfd.c:224` | (a) | [P](2026-10-05-p-pipes.md) 9: blocking reads: a second task |
| `eventfd_read.iocb_nowait` | false | `fs/eventfd.c:225` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `eventfd_write.blocking` | true | `fs/eventfd.c:264` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `ep_clear_and_put.poll_wait_active` | true | `fs/eventpoll.c:1108` | (c) | epoll nested-set release orders and the nested attach failure |
| `eventpoll_release_file.last_reference` | true | `fs/eventpoll.c:1320` | (c) | epoll nested-set release orders and the nested attach failure |
| `ep_poll_callback.scanning` | true | `fs/eventpoll.c:1466` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: the `ovflist`: needs a second CPU or thread |
| `ep_poll_callback.wq_active` | true | `fs/eventpoll.c:1482` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: a sleeper on `ep->wq`: tier 2 |
| `ep_poll_callback.pollfree` | true | `fs/eventpoll.c:1517` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: `POLLFREE`: signalfd, aio |
| `ep_attach_file.no_head_race` | true | `fs/eventpoll.c:1729` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: the race arm: `invariant` |
| `ep_register_epitem.attach_error_tep` | true | `fs/eventpoll.c:1805` | (c) | epoll nested-set release orders and the nested attach failure |
| `ep_insert.epollwakeup` | true | `fs/eventpoll.c:1855` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: `EPOLLWAKEUP` with `CONFIG_PM_SLEEP` off |
| `ep_insert.wq_active` | true | `fs/eventpoll.c:1891` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: as above |
| `ep_modify.epollwakeup` | true | `fs/eventpoll.c:1927` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: as above |
| `ep_modify.no_wakeup_source` | true | `fs/eventpoll.c:1928` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: as above |
| `ep_modify.has_wakeup_source` | true | `fs/eventpoll.c:1930` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: as above |
| `ep_modify.wq_active` | true | `fs/eventpoll.c:1967` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: as above |
| `ep_deliver_event.put_fault` | true | `fs/eventpoll.c:2030` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: `-EFAULT`: the guest's buffer is valid |
| `ep_timeout_to_timespec.zero` | false | `fs/eventpoll.c:2111` | (a) | [epoll](2026-10-12-epoll-design.md) 9.1: tier 1 is timeout 0 |
| `ep_poll.timeout_nonzero` | true | `fs/eventpoll.c:2171` | (a) | [epoll](2026-10-12-epoll-design.md) 9.1: as above |
| `ep_poll.timed_out` | false | `fs/eventpoll.c:2205` | (a) | [epoll](2026-10-12-epoll-design.md) 9.1: as above |
| `do_epoll_create.file_error` | true | `fs/eventpoll.c:2426` | (a) | [A](2026-10-05-a-alloc.md) 10: an allocation outcome, the steered site is `ep_alloc` |
| `epoll_mutex_lock.blocking` | false | `fs/eventpoll.c:2470` | (c) | epoll nested-set release orders and the nested attach failure |
| `ep_set_busy_poll_napi_id.not_busy` | false | `fs/eventpoll.c:663` | (a) | [epoll](2026-10-12-epoll-design.md) 9.2: sockets as targets |
| `ep_done_scan.ovflist_iter` | true | `fs/eventpoll.c:925` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: as above |
| `ep_done_scan.not_linked` | true | `fs/eventpoll.c:932` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: as above |
| `ep_done_scan.wq_active` | true | `fs/eventpoll.c:957` | (a) | [epoll](2026-10-12-epoll-design.md) 9.3: as above |
| `kill_fasync.has_list` | true | `fs/fcntl.c:1151` | (a) | [P](2026-10-05-p-pipes.md) 9: FASYNC/SIGIO stays `unsupported` |
| `file_f_owner_release.has_owner` | true | `fs/fcntl.c:121` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `__do_sys_fcntl.fmode_path` | true | `fs/fcntl.c:581` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `setfl.fop_check_flags` | true | `fs/fcntl.c:67` | (a) | [P](2026-10-05-p-pipes.md) 9: no `check_flags` op on the fixture's files |
| `setfl.fop_fasync` | true | `fs/fcntl.c:75` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `__fget_light.single_owner` | false | `fs/file.c:1121` | (c) | second-task and table-resize arms of the descriptor table |
| `file_needs_f_pos_lock.fmode_atomic_pos` | true | `fs/file.c:1156` | (c) | regular-file arms in shared FS code |
| `do_dup2.fd_is_open` | true | `fs/file.c:1229` | (c) | second-task and table-resize arms of the descriptor table |
| `alloc_fdtable.over_nr_open` | true | `fs/file.c:126` | (a) | [A](2026-10-05-a-alloc.md) 10: the `nr_open` limit: sizes beyond the fixture are allocation outcomes |
| `expand_fdtable.files_shared` | true | `fs/file.c:196` | (c) | second-task and table-resize arms of the descriptor table |
| `expand_files.resize_in_progress` | true | `fs/file.c:239` | (c) | second-task and table-resize arms of the descriptor table |
| `alloc_fd.slot_not_null` | true | `fs/file.c:539` | (c) | second-task and table-resize arms of the descriptor table |
| `fd_install.resize_in_progress` | true | `fs/file.c:605` | (c) | second-task and table-resize arms of the descriptor table |
| `__fget_files_rcu.masked` | true | `fs/file.c:993` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `alloc_empty_file.not_capable` | true | `fs/file_table.c:223` | (a) | [P](2026-10-05-p-pipes.md) 9: the guest is root |
| `__fput.fasync` | true | `fs/file_table.c:463` | (a) | [P](2026-10-05-p-pipes.md) 9: FASYNC |
| `__fput.not_fmode_path` | true | `fs/file_table.c:470` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `__fput.need_unmount` | true | `fs/file_table.c:477` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `fput.not_opened` | true | `fs/file_table.c:522` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `file_free.backing` | true | `fs/file_table.c:93` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `relatime_need_update.not_relatime` | false | `fs/inode.c:1944` | (c) | regular-file arms in shared FS code |
| `generic_update_time.s_version` | true | `fs/inode.c:2041` | (c) | regular-file arms in shared FS code |
| `inode_update_time.has_update_time` | true | `fs/inode.c:2054` | (c) | regular-file arms in shared FS code |
| `timestamp_truncate.gran_one` | false | `fs/inode.c:2622` | (c) | regular-file arms in shared FS code |
| `put_file_access.fmode_writer` | true | `fs/internal.h:118` | (c) | regular-file arms in shared FS code |
| `filp_flush.file_count_zero` | true | `fs/open.c:1526` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `filp_flush.fop_flush` | true | `fs/open.c:1532` | (c) | file kinds absent from the fixture (O_PATH, mounts, character devices, backing files, files with a flush op) |
| `do_pipe2.copy_to_user_failed` | true | `fs/pipe.c:1026` | (a) | [A](2026-10-05-a-alloc.md) 10: the usercopy trio are trace inputs, not fault injection |
| `pipe_read.whole` | true | `fs/pipe.c:312` | (a) | [P](2026-10-05-p-pipes.md) 9: `PIPE_BUF_FLAG_WHOLE`: notification pipes, `CONFIG_WATCH_QUEUE` unset |
| `pipe_read.confirm_error` | true | `fs/pipe.c:321` | (a) | [P](2026-10-05-p-pipes.md) 9: no `confirm` op on an anonymous pipe buffer |
| `pipe_read.o_nonblock` | false | `fs/pipe.c:356` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `pipe_read.iocb_nowait` | false | `fs/pipe.c:357` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `pipe_read.wake_next_reader` | true | `fs/pipe.c:403` | (c) | second-task and table-resize arms of the descriptor table |
| `pipe_write.loop_no_readers` | true | `fs/pipe.c:498` | (c) | second-task and table-resize arms of the descriptor table |
| `pipe_write.short_copy_count` | true | `fs/pipe.c:541` | (a) | [A](2026-10-05-a-alloc.md) 10: a usercopy fault |
| `pipe_write.o_nonblock` | false | `fs/pipe.c:557` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `pipe_write.iocb_nowait` | false | `fs/pipe.c:558` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `pipe_write.wake_next_writer` | true | `fs/pipe.c:604` | (c) | second-task and table-resize arms of the descriptor table |
| `pipe_write.update_time_error` | true | `fs/pipe.c:608` | (c) | regular-file arms in shared FS code |
| `alloc_pipe_info.not_capable` | true | `fs/pipe.c:802` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `alloc_pipe_info.soft_unprivileged` | true | `fs/pipe.c:807` | (a) | [P](2026-10-05-p-pipes.md) 9: as above |
| `create_pipe_files.writer_error` | true | `fs/pipe.c:941` | (a) | [A](2026-10-05-a-alloc.md) 10: an allocation outcome |
| `create_pipe_files.reader_error` | true | `fs/pipe.c:952` | (a) | [A](2026-10-05-a-alloc.md) 10: as above |
| `rw_verify_area.negative_pos` | true | `fs/read_write.c:459` | (c) | regular-file arms in shared FS code |
| `rw_verify_area.pos_overflow` | true | `fs/read_write.c:464` | (c) | regular-file arms in shared FS code |
| `new_sync_write.ppos` | true | `fs/read_write.c:592` | (c) | regular-file arms in shared FS code |
| `fdput_pos.pos_unlock` | true | `include/linux/file.h:77` | (c) | regular-file arms in shared FS code |
| `file_start_write.not_regular` | false | `include/linux/fs.h:2998` | (c) | regular-file arms in shared FS code |
| `file_end_write.not_regular` | false | `include/linux/fs.h:3018` | (c) | regular-file arms in shared FS code |
| `iocb_flags.o_dsync` | true | `include/linux/fs.h:3597` | (c) | regular-file arms in shared FS code |
| `iocb_flags.o_sync` | true | `include/linux/fs.h:3599` | (c) | regular-file arms in shared FS code |
| `__vlan_get_protocol_offset.vlan_type` | true | `include/linux/if_vlan.h:612` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P10: a VLAN-tagged skb |
| `pipe_buf_confirm.no_confirm` | false | `include/linux/pipe_fs_i.h:230` | (c) | regular-file arms in shared FS code |
| `__refcount_add.old_zero` | true | `include/linux/refcount.h:189` | (a) | [census 2026-10-06](2026-10-06-wireguard-census.md) P14: refcount saturation: structurally dead |
| `__seccomp_filter.trace_no_tracer` | false | `kernel/seccomp.c:1289` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `TRACE` with a tracer |
| `__seccomp_filter.case_user_notif` | true | `kernel/seccomp.c:1326` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `USER_NOTIF` |
| `__seccomp_filter.kill_last_thread` | false | `kernel/seccomp.c:1351` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: a second thread |
| `__secure_computing.case_dead` | true | `kernel/seccomp.c:1397` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.2: `MODE_DEAD` |
| `seccomp_set_mode_filter.new_listener` | true | `kernel/seccomp.c:1985` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `NEW_LISTENER` |
| `seccomp_set_mode_filter.tsync_lock` | true | `kernel/seccomp.c:2004` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `TSYNC` |
| `seccomp_set_mode_filter.tsync_unlock` | true | `kernel/seccomp.c:2027` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `TSYNC` |
| `seccomp_is_const_allow.next_insn` | false | `kernel/seccomp.c:776` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.3: the `WARN_ON` fall-off |
| `seccomp_attach_filter.tsync` | true | `kernel/seccomp.c:929` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `TSYNC` |
| `seccomp_attach_filter.wait_killable_recv` | true | `kernel/seccomp.c:946` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `WAIT_KILLABLE_RECV` |
| `seccomp_attach_filter.tsync_sync` | true | `kernel/seccomp.c:959` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.1: `TSYNC` |
| `complete_signal.not_coredump` | true | `kernel/signal.c:1041` | (c) | signal arms outside the widening's written list |
| `__send_signal_locked.queued` | false | `kernel/signal.c:1120` | (a) | [A](2026-10-05-a-alloc.md) 10: the sigqueue allocation failing |
| `__send_signal_locked.case_priv` | true | `kernel/signal.c:1136` | (c) | signal arms outside the widening's written list |
| `__send_signal_locked.multiprocess` | true | `kernel/signal.c:1171` | (a) | P9 widening [USER 2026-10-13], the design's section 16 list: group delivery |
| `send_signal_locked.has_si_pid_and_uid` | true | `kernel/signal.c:1227` | (c) | signal arms outside the widening's written list |
| `force_sig_info_to_task.was_blocked` | true | `kernel/signal.c:1345` | (c) | signal arms outside the widening's written list |
| `force_sig_info_to_task.not_sigpending` | true | `kernel/signal.c:1357` | (c) | signal arms outside the widening's written list |
| `__sigqueue_alloc.q_null` | true | `kernel/signal.c:434` | (a) | [A](2026-10-05-a-alloc.md) 10: as above |
| `prepare_signal.kernel_stop` | true | `kernel/signal.c:915` | (a) | P9 widening [USER 2026-10-13], the design's section 16 list: stop and continue signals |
| `prepare_signal.sigcont` | true | `kernel/signal.c:923` | (a) | P9 widening [USER 2026-10-13], the design's section 16 list: as above |
| `bpf_prog_store_orig_filter.filter_nomem` | true | `net/core/filter.c:1165` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.3: the `-ENOMEM` arm of an allocation site |
| `bpf_migrate_filter.old_prog_nomem` | true | `net/core/filter.c:1279` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.3: as above |
| `bpf_migrate_filter.realloc_nomem` | true | `net/core/filter.c:1293` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.3: as above |
| `bpf_prog_create_from_user.store_orig_err` | true | `net/core/filter.c:1448` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.3: as above |
| `bpf_convert_filter.seen_ld_abs` | true | `net/core/filter.c:617` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.2: unreachable after `seccomp_check_filter` |
| `bpf_convert_filter.case_ldx_msh` | true | `net/core/filter.c:794` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.2: as above |
| `bpf_convert_filter.case_len` | true | `net/core/filter.c:872` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.2: as above |
| `bpf_convert_filter.seen_ld_abs_len` | true | `net/core/filter.c:900` | (a) | [seccomp](2026-10-12-seccomp-design.md) 9.2: as above |

### 3.1 Category (c) resolved

The 49 rows the run marked (c) were examined one by one [AGENT, fork of the
coordinator 2026-10-13]: one was reachable and is closed by a trace, 37 had a
reason and are (a), 2 are closed on `task/receive-fixes`, and 9 remain,
each reachable only with a harness, steering or guest change named below. The
section 1-2 raw counts predate the trace and shift by one (842 -> 843
exercised, 139 -> 138 witnessable-unexercised, `noise.c` by one).

**Closed by a trace (1).**
- `wg_noise_expire_current_peer_keypairs.current_keypair` (noise.c:193):
  `d3_privkey_change_expires` (scripts/wg-d3-corpus.py) -- a session, then a
  private-key change (set_device, netlink.c:575) expires the peer's current
  keypair. Agrees on s2 (1 trace, 7 ops, 40 operand pairs); commit 9193c5e.

**Reclassified to (a): structurally dead, the reason in the mirror (4).**

| Decision | Outcome | Site | Reason |
|---|---|---|---|
| `wg_noise_handshake_consume_response.state_changed` | true | noise.c:790 | single-CPU: the state re-check under the write lock cannot differ from the pre-copy state, nothing runs between the two reads in a softirq (Handshake.lean `consumeResponse`). As P14. |
| `wg_noise_received_with_keypair.changed` | true | noise.c:269 | single-CPU: the double-check under `keypair_update_lock` sees the same `next_keypair` (Keypair.lean `receivedWithKeypair`). |
| `wg_socket_send_skb_to_peer.inet6` | false | socket.c:181 | a data send needs a current keypair, which a peer obtains only with an endpoint (configured, or learned from the initiation that created the session); the endpoint-less `else` arm is unreachable on the data path. |
| `do_dup2.fd_is_open` | true | file.c:1229 | the `-EBUSY` arm needs a reserved-but-uninstalled fd slot (bitmap set, `fd[]` NULL), which only a concurrent opener produces; single-task it is unreachable. The `false` arm is exercised by `p_dup_ends`. |

**Reclassified to (a): fixture-excluded, one sentence each in the P design section 9 (33).**
- regular-file arms in shared FS code (16): the fixture opens pipes, eventfds, anonymous inodes and sockets only, never a regular file (P 1, P 9).
- file kinds absent from the fixture (9): O_PATH, mounts, character devices, backing files, files with a flush op -- the same (P 9).
- second-task and table-resize arms (8): `expand_fdtable.files_shared`, `expand_files.resize_in_progress`, `fd_install.resize_in_progress`, `__fget_light.single_owner`, `pipe_write.loop_no_readers`, the `wake_next_*` arms, and `alloc_fd.slot_not_null` (an invariant) -- all need a second task or a descriptor-table resize beyond the single-task fixture (P 9).

**Closed on `task/receive-fixes` (2).**
- `wg_packet_consume_data.epipe` and `enqueued_epipe` (receive.c:528-530): the
  receive-side decrypt-ring-full drop, modelled with a 1025-message trace by
  the receive correspondence-audit fix fork.

**Residual (c): reachable only with a harness, steer or guest change (9), reported not built.**

| Decision | Site | What it needs |
|---|---|---|
| `ep_clear_and_put.poll_wait_active` | eventpoll.c:1108 | a nested set reaching its last reference while still poll-watched; the existing nested traces keep the inner alive through the outer's epitem, so the drop-outer-link-then-inner-last-ref ordering with the wait still active is not hit -- a constructed nested-release trace. |
| `eventpoll_release_file.last_reference` | eventpoll.c:1320 | the same nested-release ordering. |
| `ep_register_epitem.attach_error_tep` | eventpoll.c:1805 | the nested target's `ep_attach_file` failing; `harness/steer.py` has an alloc site for the primary attach only -- a steer site for the nested attach. |
| `epoll_mutex_lock.blocking` | eventpoll.c:2470 | the non-blocking (`trylock`) variant, reached only from a call site passing `nonblock=true`; no in-domain trace drives one -- confirm a call site or move to (a). |
| `force_sig_info_to_task.was_blocked` | signal.c | SIGSYS blocked in the child before a TRAP -- a guest op to block the signal in the sandboxed child. |
| `force_sig_info_to_task.not_sigpending` | signal.c | SIGSYS already pending before a TRAP -- two TRAPs before delivery. |
| `complete_signal.not_coredump` | signal.c | a default-action (coredumping) SIGSYS, i.e. a seccomp kill with SIG_DFL, not a handler. |
| `__send_signal_locked.case_priv` | signal.c | a kernel-originated (SEND_SIG_PRIV) signal path beyond the forced SIGSYS the corpus drives. |
| `send_signal_locked.has_si_pid_and_uid` | signal.c | the same; the signal's `si_pid`/`si_uid` metadata arm. |

The five signal arms belong to the seccomp signal path and the section-16
widening (seccomp design); each needs the blocked/pending precondition or a
default-action kill, a guest or corpus extension. The four epoll arms are
nested-set release and lock orderings a constructed trace or a steer site
would reach. None is a mirror defect: every residual arm is modelled with an
explicit outcome, only unexercised.


## 4. Unobservable outcomes

The 1783 unobservable outcomes are listed per file above. Two sub-classes matter:

- 1219 were taken by some trace: the outcome is checked by its sibling's witness, by the
  declared operands, or by the observation; the count says only that no instrumentation
  point of its own exists.
- 564 were never taken. 46 of them belong to the 23 decisions below, declared and
  never evaluated by any trace, with no witness on either side; the rest are the untaken
  fall-through sides of one-sided decisions whose other side was exercised.

| Site | Decision | Why it is never evaluated |
| --- | --- | --- |
| `drivers/net/wireguard/socket.c:270` | `endpoint_eq.b_unset` | an endpoint comparison with the second side unset: dead with the fixture's endpoints |
| `fs/eventpoll.c:2091` | `ep_send_events.first_error` | a delivery error on the first event: `-EFAULT`, epoll 9.3 |
| `fs/file.c:1157` | `file_needs_f_pos_lock.count_above_one` | shared `files_struct`: a second task |
| `fs/file.c:1157` | `file_needs_f_pos_lock.iterate_shared` | directories |
| `fs/file.c:128` | `alloc_fdtable.below_wanted` | a table smaller than wanted after rounding: structurally dead for the fixture sizes |
| `fs/file_table.c:469` | `__fput.has_cdev` | character devices |
| `fs/pipe.c:1366` | `pipe_set_size.unprivileged` | the guest is root |
| `fs/pipe.c:329` | `pipe_read.fault_no_ret` | a usercopy fault with nothing read |
| `fs/pipe.c:500` | `pipe_write.epipe_no_ret` | `-EPIPE` with nothing written: a reader closing mid-write (second task) |
| `fs/pipe.c:542` | `pipe_write.fault_no_ret` | a usercopy fault with nothing written |
| `fs/pipe.c:782` | `too_many_pipe_buffers_hard.over_limit` | the hard limit: the guest is root |
| `fs/pipe.c:787` | `pipe_is_unprivileged_user.not_cap_sys_resource` | the guest is root |
| `fs/pipe.c:787` | `pipe_is_unprivileged_user.not_cap_sys_admin` | the guest is root |
| `fs/pipe.c:812` | `alloc_pipe_info.hard_unprivileged` | the guest is root |
| `kernel/seccomp.c:1006` | `seccomp_log.case_allow` | `seccomp_log` for `ALLOW`: the function is branch-free, its arms plain |
| `kernel/seccomp.c:1017` | `seccomp_log.case_user_notif` | `USER_NOTIF`, seccomp 9.1 |
| `kernel/seccomp.c:1018` | `seccomp_log.user_notif_requested` | as above |
| `kernel/seccomp.c:2113` | `do_seccomp.case_default` | an unknown `seccomp` operation: the validator rejects it |
| `kernel/seccomp.c:820` | `seccomp_is_const_allow.jcond_default` | an unknown jump condition after the checker: dead |
| `kernel/signal.c:1148` | `__send_signal_locked.overflow_not_special` | sigqueue overflow of a non-special signal: allocation |
| `kernel/signal.c:991` | `wants_signal.not_sigpending` | a task with the signal already pending |
| `net/core/filter.c:677` | `bpf_convert_filter.alu_mode_abs` | `BPF_ABS` on an ALU: unreachable after `seccomp_check_filter` |
| `net/core/filter.c:887` | `bpf_convert_filter.case_default` | an unknown classic opcode after the checker: dead |

## 5. Exclusions in force

All from `correspondence/kcov.json` (version 2). Each is justified by a
measurement of the built code or a decision in the register; an exclusion
with no justification, or one that no longer removes a problem, is cut
(AGENTS.md, "Gates and speedbumps").

### 5.1 Operand exclusions (7)

| Decision | Operand | Call site | Justification |
| --- | --- | --- | --- |
| `__refcount_add.old_zero` | `root_user.__count` | `fs/pipe.c:794` | `get_current_user()` inlined into `alloc_pipe_info`; the guest-wide root credential count (26 or 27, kernel threads included); the outcome is checked, the value is not the trace's (P design) |
| `__refcount_add.old_zero` | `root_user.__count` | `fs/eventpoll.c:2412` | the same count at `ep_alloc`'s `get_current_user()` inlined into `do_epoll_create` (epoll stream S) |
| `do_epoll_ctl.gen_matches` | `loop_check_gen` | `fs/eventpoll.c:2552` | the boot-global counter, two higher after every full check of every trace of a boot; the mirror's counter is relative to the fixture's warm-up (epoll design 3.5) |
| `ep_loop_check_proc.visited` | `loop_check_gen` | `fs/eventpoll.c:2302`, `:2315` | the absolute counter in the in-check visited test and its recursion site, inlined one level (epoll stream S) |
| `ep_get_upwards_depth_proc.visited` | `loop_check_gen` | `fs/eventpoll.c:2344`, `:2347` | the absolute counter in the upward walk's visited test and its recursion site (epoll stream S) |

Pays its way: each removes a value the mirror cannot know (a guest-wide
count, a boot-global counter) while the outcome stays checked. The
presence-form check (a row at a declared call, not one per report, since
the guest deduplicates identical rows) is the register's 2026-10-12 entry.

### 5.2 Shared exits (7)

| Function | Frames | Unless covered | Justification |
| --- | --- | --- | --- |
| `file_end_write` | `fs.h:3018` at `read_write.c:691` | `read_write.c:691` | `vfs_write`'s early returns jump into the epilogue's KCOV point (the merged-return-block class, P design) |
| `__file_update_time` | `inode.c:2240` at `:2275` | `fs.h:1166`, `inode.c:2241`, `:2275` | `file_update_time`'s "nothing" return shares its block with the inlined helper (representation batch, pipes-20260920-00110) |
| `bpf_migrate_filter` | `filter.c:1320` at `:1363` | `filter.c:1263`, `:1363` | `bpf_prepare_filter`'s error return after a refused program shares the inlined `out_err` (seccomp X) |
| `seccomp_get_notif_sizes` | `seccomp.c:2088` at `:2111` and up | `seccomp.c:2079`, `:2111`, … | `do_seccomp`'s return block shared with the inlined query (seccomp X) |
| `ep_modify` | `eventpoll.c:1979` at `:2604` | `eventpoll.c:1952`, `:2604` | `ep_insert`'s and `ep_modify`'s identical tails are one block in the built code (epoll S) |
| `fdput` (2 points) | `file.h:62` at `eventpoll.c:2680` | `eventpoll.c:2674` | `do_epoll_wait`'s `-EBADF` jumps into the error-path `fdput` epilogue, two points of one chain (epoll S) |
| `ep_register_epitem` | `irqflags.h:42…` at `eventpoll.c:1808`, `:1845`, `:2584` | `eventpoll.c:1800`, `:1845`, `:2584` | the two `percpu_counter_dec` calls are one block (epoll S, the steered epitem failure) |

Each names a measured merged block; the "unless covered" point is the
block's own entry, so the exemption applies only when the early return is
the path taken. Hit counts this run: 1597 early returns through a declared shared exit (A: 21, D: 1576, the rest 0); the operand exclusions fired 1049 (`root_user.__count`), 764, 287 and 121 times (`loop_check_gen`).

### 5.3 Branch-free functions (12)

| Function | Justification |
| --- | --- |
| `fls128` | arithmetic helper, no branch of its own (allowedips) |
| `INET_ECN_decapsulate`, `__INET_ECN_decapsulate`, `INET_ECN_set_ce`, `INET_ECN_set_ect1`, `IP_ECN_set_ce`, `IP_ECN_set_ect1`, `IP6_ECN_set_ce`, `IP6_ECN_set_ect1` | the ECN helpers compile branchless (W5-W6 receive: mask arithmetic) |
| `seccomp_may_assign_mode` | measured: compiled differently per inlined caller, no point of its own (seccomp V) |
| `seccomp_log` | measured: no point of its own (seccomp V) |
| `percpu_counter_compare` | measured: the `count_gt` compare folded (epoll S) |

A branch-free function may carry decisions declared `plain`; it is exempt
only from the rule that a decision's C function must own instrumentation.

### 5.4 Data-only operations (2)

`seccomp_prctl`, `seccomp_capdrop`: their kernel work is entirely in
unlisted files (`kernel/sys.c`, the capability code), so they are exempt
from "no coverage in anchored files" and "no model decision" only; any
decision they report once a mode is set is checked (seccomp design 6.3,
audit C4).

### 5.5 Known gaps (0)

The `known_gaps` list is empty: no per-operation line exemption is in force.
The designs' "modelled but unexercised" items are decisions the mirror
emits and no trace witnesses, listed in section 3 as category (a), not gaps.

### 5.6 Exclusions that no longer pay

None. Every exclusion in force removed a problem in this run or in the run that
introduced it, and each names its measurement: the seven operand exclusions fired
2221 times, the shared exits were reached 1597 times by an early return (the report's
counter is aggregate: it does not say which of the seven fired; the seccomp group's 21
can only be the two seccomp exits, the epoll-and-pipes group's 1576 the FS ones), the
twelve branch-free functions carry decisions whose C functions own no point,
and the two data-only operations have no anchored coverage by construction. One
exclusion is missing rather than stale: `dstCacheHit` is undeclared because
`net/core/dst_cache.c` is not anchored (item 8 deferral); anchoring it is a small stream.

### 5.7 List-primitive internals, at the altitude (added 2026-10-15)

The inlined tests inside the kernel's list and queue primitives are not
choice points of the mirror, whose state is list-shaped: `hlist_add_head_rcu`'s
`if (first)` (rculist.h, at peerlookup.c:39, :157), `hlist_replace_rcu`'s
`if (new->next)` (at :178), `skb_queue_splice_init`'s and
`skb_queue_splice`'s `!skb_queue_empty` (send.c:351, :407; the first is the
test at :353, the second is always true after it), `__skb_queue_purge`'s
dequeue loop (:338, which only frees), and `skb_orphan`'s
`if (skb->destructor)` (:400, which releases the sending socket's buffer
charge below WireGuard's boundary, unobservable under the fixture's
`SO_SNDBUFFORCE`). The `hlist_unhashed` test of `hlist_del_init_rcu` is the
exception: it decides whether an entry leaves a table, and the mirror
reports it at every remove and insert (`.idxRemoveHashed`,
`.idxInsertHashed`, `.pubkeyRemoveHashed`). From the Send audit's F4 and the
Peer audit's altitude note (`docs/2026-10-15-audit-send.md`,
`docs/2026-10-15-audit-peer.md`).

## 6. The anchored-file boundary

41 files are anchored (`kcov.json` `files`): a decision may be declared in
them, and a PC in them outside any listed function is a problem. Everything
else is environment: its effects reach the mirror only through recorded
hidden inputs (the choice stream), observations, or named cuts.

### 6.1 Anchored

| File | Why it is anchored |
| --- | --- |
| `drivers/net/wireguard/{allowedips,peer,noise,netlink,socket,peerlookup,cookie,device,send,queueing,receive,timers,ratelimiter}.c`, `queueing.h` | the target: single-CPU WireGuard, every function listed or a named cut |
| `include/crypto/curve25519.h` | the inline key-validity test on the WireGuard paths |
| `include/linux/if_vlan.h`, `include/net/ip_tunnels.h`, `include/net/inet_ecn.h` | inline helpers `wg_xmit` and the receive path call, with instrumentation points of their own |
| `fs/pipe.c`, `include/linux/pipe_fs_i.h`, `fs/inode.c`, `include/linux/time64.h` | the pipes scale test and the timestamp update it drives |
| `fs/file.c`, `fs/fcntl.c`, `fs/open.c`, `fs/read_write.c`, `fs/anon_inodes.c`, `fs/file_table.c`, `fs/internal.h`, `include/linux/fs.h`, `include/linux/file.h`, `include/linux/refcount.h` | the file-descriptor slice the FS operations run through |
| `fs/eventfd.c` | eventfd, the first producer |
| `fs/eventpoll.c`, `include/linux/eventpoll.h`, `include/linux/poll.h`, `include/linux/percpu_counter.h`, `arch/x86/include/asm/irqflags.h` | epoll and the inline helpers its paths own points in |
| `kernel/signal.c` | signal generation down to the pending set (pipes' SIGPIPE, P9) and the seccomp SIGSYS extension (P9 widening, 2026-10-13) |
| `kernel/seccomp.c`, `net/core/filter.c` | seccomp proper and the classic-BPF checker and translation |

### 6.2 Environment, referenced by the mirror's site or decision tables

| File | Treated as |
| --- | --- |
| `kernel/bpf/core.c` | the eBPF engine, a service with an ISA contract (`Leanux/Seccomp/Engine.lean`); the user's JIT project owns it |
| `net/netlink/af_netlink.c` | the netlink transport; its three decisions would anchor code the mirror treats as environment [AGENT 2026-10-12, W2] |
| `kernel/fork.c` | the child's creation: two clock records consumed at `copy_process` |
| `fs/ioctl.c` | the consumer frames of the virtual-time advance and the kind-310 end-of-wait read |
| `net/core/dst_cache.c`, `include/net/dst_cache.h` | the destination cache: its hit test is modelled on `UInt64` jiffies, its decision `dstCacheHit` undeclared until the file is anchored (item 8 deferral) |
| `net/ipv4/route.c`, `net/ipv4/udp.c`, `net/ipv4/ip_output.c`, `net/ipv4/icmp.c`, `net/core/dev.c`, `net/core/sock.c`, `net/core/neighbour.c`, `net/core/flow_dissector.c`, `drivers/net/loopback.c` | the IP stack beyond WireGuard's boundary [USER 2026-10-07]: reached only where WireGuard's observables depend on it, as hidden inputs or observations |
| `net/ipv4/inet_hashtables.c`, `net/core/net_namespace.c` | the random port draw and the namespace lifecycle: recorded hidden inputs |
| `lib/rhashtable.c`, `mm/vmalloc.c` | allocation and rehash internals: recorded outcomes or unrecorded-by-construction sites |
| `kernel/sched/wait.c` | built without KCOV (`KCOV_INSTRUMENT := n`): the wake walk's tests are mirror control flow observed through the callbacks it runs (epoll Q) |
| `kernel/sys.c` | `prctl` dispatch and `capset`: data-only operations |
| `include/linux/ptr_ring.h`, `include/linux/seqlock.h`, `include/linux/jiffies.h`, `include/linux/wait.h` | inline primitives whose decisions are attributed to the WireGuard or FS line that inlines them |
| `fs/libfs.c`, `fs/namei.c`, `lib/kobject_uevent.c`, `kernel/sched/deadline.c`, `net/ipv6/sit.c` | named cuts (no decisions; recorded only when a chunk arms the range) |

## 7. W13

The [census of 2026-10-06](2026-10-06-wireguard-census.md) defined W13 as
"a second device (`wg1`); `wg0`↔`wg1` as a real peer pair", size L, placed
last by the [pause-state note](2026-10-08-pause-state.md) (section 3). No
design exists for it; every mention since is a boundary note.

**Already covered by later work.**
- Per-device rings and queues: the representation batch's ptr_ring with
  cursors and the packet store with ids are per device by construction;
  the W7 tier shows the ring's occupancy rule exact (W4-W7 section 9 listed
  "a second device sharing nothing" under W13 because rings are per
  device).
- Lifetime identities for peers, keypairs and packets: a second device's
  objects get distinct identities without a representation change.
- The dispatch budget: `KCOV_DISPATCH_MAX` is 32 (D3+A); a second device
  adds no symbol, since the dispatch table keys the work function, not the
  device, and the kind-300 unit word already names the dispatched work
  item.
- Timers and virtual time (items 7 and 8): per peer, device-independent.
- `wg_netns_pre_exit` iterates `device_list` (W8); the netlink `-ENODEV`
  for `wg1` is in W2's corpus.

**What remains.**
- The kernel state: `Kernel.wg : Option WG.Device` (`Leanux/Kernel/Defs.lean:605`)
  becomes a map keyed by ifindex with the current device selected per path
  (the socket's `sk_user_data` on receive, the netlink lookup on configure,
  the net device on transmit); `device_list` ordering for `wg_netns_pre_exit`;
  the ratelimiter's `users` refcount (modelled as data, L section 9) taking
  the second init and the first uninit.
- The paths: `wg_receive` demultiplexing by socket; a datagram sent by
  `wg0`'s transmit worker through loopback into `wg1`'s socket, which puts
  both devices' NAPI polls into one `net_rx_action` (today `napiSoftirq`
  keeps `unsupported` for two pending NAPIs, W4-W7 16.2: this is the one
  environment rule W13 must open, and the records already carry the NAPI
  identity).
- The fixture: a second `wg_create` (opcode 15 exists) with its own
  private key, listen port and address; peers configured on each device
  with the other's public key and `127.0.0.1:port` endpoint; the generator's
  peer and endpoint tables widened; the trace validator's single-device
  assumptions (the stepped dump's descriptor, the inject target).
- The corpus: handshake and data in both directions between the two devices,
  a session where the responder is the guest's other device (which would
  also exercise `wg_noise_received_with_keypair.changed`, category (c)
  above), delete and down of one device while the other has a session.

**Mirror modules and kernel paths.** `Leanux/Kernel/Defs.lean`,
`Leanux/WG/State.lean`, `Device.lean`, `Socket.lean` (`wg_receive`'s socket
lookup), `Netlink.lean` (`lookup_interface`), `Leanux/Env.lean` and
`Env/Batch.lean` (two NAPIs, the loopback delivery as a recorded dispatch),
`Leanux/Runner.lean` (the per-device observation); kernel paths
`device.c` (`wg_newlink` twice, `device_list`), `socket.c` (`wg_receive`,
`send4` to a local address), `netlink.c`, `ratelimiter.c:164-200`.

**Kernel instrument.** None expected: the dispatch, NAPI and socket records
carry the identities. If the loopback delivery's placement is not determined
by the existing NET_RX section records, a record of the receiving socket
at `wg_receive` would settle it (record-only, class-approved).

**Estimate.** About 0.8 WU: the state refactor and the two-NAPI rule
(0.4), the fixture and generator (0.2), the corpus and claim point (0.2).
The earlier L was sized before per-device rings, lifetime identities and
the dispatch identity existed.
