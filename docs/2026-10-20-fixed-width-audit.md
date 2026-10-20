# Fixed-width kernel integers held as naturals: an audit

2026-10-20. One pass over the mirror's state for fields that stand in for
a C integer of fixed width while typed `Nat` or `Int`, prompted by the
binary track's executed comparison of the mirror with the compiled
kernel, which found the first of them.

## 1. The finding and the ruling

`struct allowedips::seq` is a `u64` (allowedips.h:32), set to 1 by
`wg_allowedips_init` (allowedips.c:255) and pre-incremented by every
free (:262), insert (:287, :298) and remove-by-peer (:311); the device
dump takes it at a split peer's first visit and abandons the peer's
allowed-IPs nest when it has changed (netlink.c:166-168). The mirror
held it as a natural, so from the word's maximum an insert left 2^64
where the C leaves 0. The binary track's reproducer executed the C's
insert over a reconstructed heap with the counter at its maximum and
compared the result with the mirror's (its note in the binary track's
worktree, `docs/2026-10-20-binary-allowedips.md`). The differential
check cannot reach the state: the counter needs 2^64 mutations.

The user ruled the representation a mirror defect, to be fixed at the
thin layer [USER 2026-10-20]: the field is the C's word, the increment
the word's, the comparison over the word. This note is the audit that
ruling asked for: which other fields of the mirror's state hold a C
word as a natural, and what to do about each.

## 2. Method and dispositions

Every structure field typed `Nat`, `Int`, `Option Nat` or `Option Int`
in `Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean`, `Leanux/Net`,
`Leanux/Seccomp`, `Leanux/FS` and `Leanux/Env.lean` was read against
the C it mirrors. Fields already typed as words (`UInt32`, `UInt64`,
`Int64`: the pipe ring's `head` and `tail`, the timers' jiffies, the
eventfd count, the seccomp engine's registers) are outside the pass.
For each field: the C type and declaration; whether a trace on this
fixture can reach the wrap; whether the wrapped value is observable (a
return, an observation, a branch of the C that reads it); and one of
three dispositions.

- **Fixed now**: a word on WireGuard's modelled paths whose wrap feeds
  a comparison or an observation and is not excluded by the C's own
  checks. These are the states the binary track's instrument can
  construct and compare, so the mirror must hold the word. Each has a
  case in `tests/FixedWidthTests.lean` (run by the model replays), and
  none is reachable by the differential check.
- **Declared**: the same shape of difference, but either reached only
  by a count no fixture reaches and outside the binary track's current
  scope (the file-descriptor slice), or inside the environment model.
  The mechanical fix is named; the user decides when it lands.
- **No difference**: the natural equals the C's word on every state
  the kernel can reach, because the C's own checks bound the value, the
  value comes from a fixed-width source (parsed bytes, a record, a
  configured attribute), the arithmetic is invariant under the wrap, or
  the field is not observable on this configuration.

## 3. Fixed now

| Field | C | Wrap reachable here | Observable | Fix |
|---|---|---|---|---|
| `AllowedIps.seq`, `DumpCtx.allowedipsSeq` | `u64 seq` (allowedips.h:32); `u64 allowedips_seq` (netlink.c:99) | no: 2^64 table mutations | the dump's consistency branch (netlink.c:166-168) | `UInt64`, the wrapping `+ 1` at the three increment sites |
| `Device.deviceUpdateGen`, `NlSock.prevSeq`, `DumpCall.prevSeq` | `unsigned int device_update_gen` (device.h:54); the callback's `unsigned int prev_seq, seq` (include/linux/netlink.h:292) | no: 2^32 `wg_set_device` calls | `NLM_F_DUMP_INTR` (include/net/netlink.h:1196-1198); 0 after the wrap also reads as "no previous chunk" | `UInt32` for the three |
| `Net.Fib.Table.rtGenid4` | `atomic_t rt_genid` (include/net/netns/ipv4.h:276), `rt_cache_flush` (route.c:406-409) | no: 2^32 flushes | the endpoint cache's validity (`rt_cache_valid`, route.c:1602-1607) on the send path | `UInt32`; `DstSlot.gen` keeps the word's value as a natural, since it also holds the IPv6 sernum |

The witness runs each from the word's maximum: an insert of an invalid
prefix of each family (`-EINVAL`, allowedips.c:186-187) and a free of
the empty table; a `wg_set_device` with no attributes; one
`rt_cache_flush`. Before the fix each left 2^64 or 2^32; after, 0.

## 4. Declared

| Field | C | Wrap reachable here | Observable | Mechanical fix |
|---|---|---|---|---|
| `Peer.txBytes`, `Peer.rxBytes` | `u64 rx_bytes, tx_bytes` (peer.h:52) | no: 2^64 bytes | the dump's `tx_bytes`/`rx_bytes` | `UInt64`; the increments at `Data.lean:182`, `Handshake.lean:454`, `Receive.lean:336`, `RxData.lean:59` take `.toUInt64` of the length |
| `Device.rxPackets`, `rxBytes`, `txPackets`, `txBytes` | `u64_stats_t` in `pcpu_sw_netstats` (include/linux/netdevice.h:2737-2742), one CPU | no | `wg_observe`'s stats | `UInt64`; `Socket.lean:194`, `Receive.lean:338`, `RxData.lean:57` |
| `Device.txErrors`, `txDropped`, `rxErrors`, `rxFrameErrors`, `rxLengthErrors` | `unsigned long` in `dev->stats` (64-bit here) | no | the device statistics | `UInt64` |
| `Eventpoll.gen`, `FSWorld.loopCheckGen` | `u64 gen` (fs/eventpoll.c:350), `static u64 loop_check_gen` (:394) | no: 2^64 loop checks | the visited test (`Eventpoll.lean:841`, `:877`, `:937`) | `UInt64` at `Defs.lean:408` and `:670`, the bump sites |
| `Net.Fib.Table.devAddrGenid`, `FibInfo.nhSaddrGenid` | `atomic_t dev_addr_genid` (fib_frontend.c:1458, :1463, :1505), `int nh_saddr_genid` | no: 2^32 address changes | the source-address cache's validity; the mirror already counts from 0 with the comparison's operands excluded | `UInt32` for both |
| `Routing.ipv6Gen` | `atomic_t fib6_sernum` (include/net/netns/ipv6.h:111) with `fib6_new_sernum` = `old < INT_MAX ? old + 1 : 1` (ip6_fib.c:92-99) | no: 2^31 bumps | the IPv6 endpoint cache's validity (`Socket.lean:255`) | in the environment model (`Env.lean`, seven bump sites), the IPv6 lane being deferred [USER, lane C]: the exact rule above, when that lane opens |
| reference counts: `Peer.refcount`, `Keypair.refcount`, `Eventpoll.refcount`, `EventfdCtx.kref`, `SeccompFilter.refs`/`users`, `Page.pageCount`, `Inode.iCount`/`iReadcount`/`iWritecount`, `File.fCount`, `FilesStruct.count`, `FibInfo.treeref` | `kref`/`refcount_t` (saturating at `REFCOUNT_SATURATED` with a warning, never wrapping), `atomic_t`, `atomic_long_t` | no: bounded by live references | not a wrap: saturation, far beyond any reachable count | none proposed; recorded so the class is known |
| `Inode.iIno`, `FSWorld.lastIno` | `unsigned long i_ino` from `get_next_ino` (`unsigned int`, fs/inode.c:1068, per-CPU batches) | no | unobserved (the mirror's own note at `Defs.lean:644`) | `UInt32` if the number is ever observed |

The byte and packet counters are campaign 3's conservation operands; the
retyping changes those statements' arithmetic, so it is put to the user
rather than landed here.

## 5. No difference

Grouped by the reason the natural equals the C's word.

Bounded by the C's own checks:
- `Keypair.sendingCounter` (`atomic64_t`, noise.h:33): the increment
  past `REJECT_AFTER_MESSAGES` invalidates the keypair (send.c:380-382,
  :391), and a keypair is never used again once invalid, so the counter
  never exceeds `REJECT_AFTER_MESSAGES + 1`, below 2^64 by 2^13.
- `ReplayCounter.counter` (`u64`, noise.h:19) and its `backtrack` words
  (`unsigned long[128]`): `counter >= REJECT_AFTER_MESSAGES + 1` and
  `their_counter >= REJECT_AFTER_MESSAGES` are rejected first
  (`RxData.lean:132-134`), the wire's counter is 8 bytes, and each word
  takes bits below 64 only.
- `Peer.timerHandshakeAttempts` (`unsigned int`, peer.h:56): reset at
  completion (`Handshake.lean:414`, `Send.lean:61`) and the retransmit
  stops past `MAX_TIMER_HANDSHAKES` (`Timers.lean:28-39`).
- `Device.numPeers` (`unsigned int`, device.h:54): `MAX_PEERS_PER_DEVICE`.
- `Device.handshakeQueueLen`, the `PtrRing` cursors (`int`,
  include/linux/ptr_ring.h): the C wraps them at the ring's size and
  the mirror does the same (`PtrRing.lean:31-33`, `:48-51`).
- `UserStruct.pipeBufs` (`atomic_long_t`), `UserStruct.epollWatches`
  (`percpu_counter`): the soft and hard page limits and
  `max_user_watches`.
- `Seccomp.filterCount` (`atomic_t`), `BpfProg.len`, `stackDepth`,
  `SockFprog.len`, the translation's lengths: `BPF_MAXINSNS` and
  `MAX_INSNS_PER_PATH`.
- `Eventpoll.loopCheckDepth` (`u8`, fs/eventpoll.c:352): at most 5.
- `PipeInodeInfo.maxUsage`, `ringSize`, `nrAccounted` (`unsigned int`,
  include/linux/pipe_fs_i.h:63-65): `pipe_max_size`.

From a fixed-width source (parsed bytes, a record, a configured
attribute), never advanced by arithmetic:
- `Endpoint` and `SkbSource` fields, `Peer.remoteIndex`,
  `Keypair.remoteIndex` (`__le32`), `IndexEntry.index` (the 4-byte
  draw), `TxPacket.nonce`/`RxPacket.nonce` (the bounded counter or the
  wire's 8 bytes), `ds`/`tos` (`u8`), `csum`, `Device.mtu` and
  `Route.mtu` (`int`, checked against the MTU bounds),
  `Device.incomingPort` (`u16`), `Device.fwmark` (`u32`),
  `Peer.persistentKeepaliveInterval` (`u16`), `Peer.handshakeState`
  (an enum), `Device.ifindex`, `Device.sock4`/`sock6` (ports),
  `Epitem.fd` (`int`), `Eventpoll.busyPollUsecs` (`u32`),
  `Timespec64.tvSec`/`tvNsec` (validated by `timespec64_valid`),
  `SeccompData.nr` (`int`, reduced at `Engine.lean:95-96`),
  `FibInfo` and `FibAlias` attributes (`protocol`, `scope`, `flags`,
  `priority`, `prefsrc`, `tbId`, `mtu`, `oif`, `dev`, `nhScope`,
  `nhFlags`, `nhSaddr`, `slen`, `dscp`, `faDefault`), the datagram
  records' addresses and ports.

Invariant under the wrap:
- `Eventpoll.seq` (`seqcount_spinlock_t`, an `unsigned int`): bumped by
  2 and read as parity and equality (`Eventpoll.lean:233`, `:254`,
  `:763-769`), both the same modulo 2^32.
- `PipeInodeInfo.rCounter`/`wCounter` (`unsigned int`): compared by
  equality only in `fifo_open`'s partner wait, which no modelled path
  runs (pipes come from `pipe2`).
- `File.fPos`, `Kiocb.kiPos` (`loff_t`): pipes and eventfds never
  advance them.

Not observable on this configuration:
- `Peer.internalId`, `Keypair.internalId`, `WGWorld.peerCounter`,
  `keypairCounter` (`u64` from `atomic64_inc_return`, peer.c:19, :42;
  noise.c:105): read by `pr_debug` (off) and by the CPU choice modulo
  one online CPU.
- `Device.handshakeLastCpu`, `encryptLastCpu`, `decryptLastCpu`,
  `Peer.serialWorkCpu` (`int`): -1 or 0 on one CPU.
- `Ratelimiter.refcnt` (`u64 init_refcnt`, ratelimiter.c:16): one
  device.

Not C words (mirror, runner or environment bookkeeping): `NodeId`,
`PeerId` and the other identities, `WheelEntry.slot`/`enqueued` and
`WGWorld.timerEnqueues` (the timer wheel's order stamps),
`FilesStruct.fdtGeneration`, `Epitem.fileAddr` (the rbtree's order
key), `Timing`, `AllocSiteInfo`, `HiddenRecord`, the workers' counts,
`netRxSections`, `napiAmbiguous`, `placeholderCount`, the fixture
facts (`nrFiles`, `maxFiles`, the pipe sysctls, `maxUserWatches`,
`pathCount`, `netIfindexNext`).

## 6. What the witness covers and what it cannot

`tests/FixedWidthTests.lean` (target `leanux-fixed-width-tests`, run by
`evaluator.test_model_replay`) constructs each world directly and runs
one increment from the word's maximum. The differential check cannot
reach any of these states on this fixture; it stays the gate for every
reachable state, and the witness is the only check of the wrap. The
binary track's reproducer is the instrument that found the first and
can test the others from constructed heaps.

## 7. Proof lag

The retyping changes the type of `peerAllowedips.seq`,
`deviceUpdateGen`, `prevSeq` and `rtGenid4` wherever a proof names
them. On main's tree the build of `LeanuxProofs` after the change
names the modules that fail; the campaign branches carry their own
frames over these fields. Both are listed in the fix's integration
report, as the lag-and-repair rule requires; the repair is a follow-on
on the proof tree, not a condition on this change.
