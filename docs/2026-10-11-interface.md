# The interface commit: files, owners and the shared tables (2026-10-11)

The base every W stream branches from (the pause note's resume order,
step 6). Each stream edits only the files it owns below; the shared
surfaces are the coordinator's, allocated here, and a stream that needs
more asks before taking it.

## Files and owners

| Stream | Design | Owns | Meets the others at |
|---|---|---|---|
| W1+W2 netlink completeness, multi-message dumps | `docs/2026-10-06-w1-w2-netlink.md` | `Leanux/WG/Netlink.lean` (get and dump paths), the `wg_get_start`/`wg_get_recv` operations (`harness/guest.c`, `harness/trace.py` fields, `evaluator/protocol.py` entries), `harness/wg.py`, `corpus/wireguard/w1_*`, `w2_*`, `scripts/wg-w12-corpus.py`, the W1/W2 mutant patterns | `Leanux/Env.lean` (the cursor state), `Leanux/Runner.lean` (the op schema) |
| W4+W7 T: transmit shapes | `docs/2026-10-06-w4-w7-transmit-bulk.md` §12, §15 | **`Leanux/Env/IpStack.lean`**, `Leanux/WG/Device.lean` (`wgXmit` GSO/trim, `wgOpen`, `Device.mtu`), `Leanux/WG/Send.lean` (`sendKeepalive`), `harness/noise.py` (the GSO builder), the `wg_xmit` options and `wg_set_mtu` in `harness/guest.c` | `Leanux/Env.lean` hooks `xmitPacket` (`xmitPackets`), `xmitMulticastLoop`, the keepalive rule |
| W4+W7 B: bulk queues | same, §12, §15 | **`Leanux/Env/Batch.lean`**, `Leanux/WG/Send.lean` (`enqueuePerDeviceAndPeer`), `Leanux/WG/Data.lean` (`txWorker`), `Leanux/WG/RxData.lean` (`rxPoll`, `enqueuePerPeerRx`), `Leanux/WG/Receive.lean` (`consumeData` arms), `wg_batch` in `harness/guest.c` (from `wg_flood`), `kcov_capacity` | `Leanux/Env.lean` hooks `flood` (`batch`), `napiSoftirq`, `napiIrqExit`, the worker runners |
| W4+W7 H: harness, corpus, the per-section operand agreement | same, §12 | `scripts/wg-w47-corpus.py`, `corpus/wireguard/w4_*`, `w7_*`, `evaluator/napi_orders.py`, **`evaluator/check.py`'s per-section agreement** (T1), the W4/W7 mutant patterns | `evaluator/check.py` (the coordinator's otherwise) |
| W5+W6 H: the receive fixture | `docs/2026-10-06-w5-w6-receive.md` §11 | the trace fields (`tos`, `from: "ll"`), the observation format, the fixture setup and the `LEANUX_FIXTURE` row, `recvmsg`, the second socket, `ipv4_tcp` and the `rst4` decoder: `harness/guest.c`, `harness/trace.py`, `harness/wg.py`, `harness/noise.py`, `harness/linux.py`, `harness/test_*.py`, `.inetEhashSecret` in `evaluator/check.py` | after this commit, before R |
| W5+W6 R: receive shapes and the RST | same | `Leanux/WG/RxData.lean`, `Leanux/WG/Device.lean` (`wgXmit`'s `ds`), `Leanux/WG/State.lean` (`Endpoint`), `Leanux/WG/Receive.lean` (`endpointFromSkb`), **`Leanux/Env/Stack.lean`** (new, R creates it), `Leanux/Kernel/Defs.lean` (one site, ids 140-149) | `Leanux/Env.lean` (sender state, `deliverSent`, `observe`, `deliverInner`) |
| W5+W6 G: generator, corpus, mutants | same | `evaluator/generate.py` (`rx_ecn`, `rx_scoped`, `stack_rst4`), `corpus/wireguard/w5_*`, `w6_*`, the W5/W6 mutant patterns | |
| W8+W9 (W8 netns exit; W9 routing) | `docs/2026-10-06-w8-w9-netns-routing.md` §10 | `Leanux/WG/Socket.lean` (W8 `socketInit`'s live arm; W9 `send4`/`send6`, `DstCache`), `Leanux/WG/Device.lean` (`wgNetnsPreExit`, `linkwatchDoDev`), `Leanux/WG/Types.lean` (`carrier`, `operUp`, `qdiscNoop`, `Peer.dstCache`), `Leanux/WG/Netlink.lean` (`setDevice`'s `EPERM`), `Leanux/Kernel/Defs.lean` (`Worker` indices 12-13, `netnsCHolders`, the mode, sites 150-169), `Leanux/Kernel/Decision.lean` (its block), the routing model in `Leanux/Env.lean` (`route4/6`, the generations, `isSender` as the wildcard bind, `senderSource` by destination, `deliverSent` with the source, `wgNetnsClose`, `runNetnsCleanup`, the mode's rules; W9 first, W8 after), `Leanux/Runner.lean` (the mode), opcodes 22-24 in `harness/guest.c`, `harness/trace.py`, `evaluator/protocol.py`, `harness/linux.py` (`DISPATCH_SYMBOLS` +2, the per-trace arm subset), `kernel/patches/choice-stream.patch` (the two kind-306 sites: a kernel change for the user's approval), `scripts/wg-w89-corpus.py`, `corpus/wireguard/w8_*`, `w9_*` | `Leanux/Env.lean` (W5+W6 R's `deliverSent` and `observe`: whichever lands second rebases) |
| W3+W12 peer removal with queued work; multi-peer timers | `docs/2026-10-06-w3-w12.md` | `Leanux/WG/PeerRemove.lean` (new), `Leanux/WG/Netlink.lean` (the removal call), `Leanux/WG/Timers.lean`, `Leanux/WG/Keypair.lean`, `Leanux/WG/Send.lean` (the `handshake_send_wq` shape), `Leanux/WG/Socket.lean` (the helpers moved from `Netlink.lean`), the timer pass in `Leanux/Env.lean` (`fireTimer`, `runTimers`, `runTimersPlaceholder`: the per-kind parallel field), `corpus/wireguard/w3_*`, `w12_*` (folded into L's), the W3/W12 mutant patterns | `Leanux/Env.lean` (the timers block) |

Shared, coordinator-owned, allocated here and append-only per stream:
- the wire opcode table (`harness/trace.py` `OPCODES`, `RESERVED_OPCODES`;
  `harness/guest.c` `OP_*`; `evaluator/protocol.py` `SEMANTIC_ERRNOS`):
  20 `wg_get_start`, 21 `wg_get_recv` (W2); 22 `wg_netns_close` (W8, taken);
  23 `wg_deladdr`, 24 `wg_delroute` (W9); W4's `wg_set_mtu` and the
  `wg_xmit`/`wg_batch` options need codes from the coordinator when T and
  B land (`OP_SET_MTU`, `OP_BATCH` placeholders in the design);
- record kind 306, the dst-cache `jiffies` records (`evaluator/check.py`
  `DST_CACHE_JIFFIES`; W9's class `jiffies`);
- `HiddenSite` ids: W5-W6 140-149, W8-W9 150-169, W1-W2 170-179, W3-W12
  180-189 (`Leanux/Kernel/Defs.lean`, each stream's own block);
- `Worker` indices 12-13 (W8-W9) and 14-15 (W5-W6), with their section
  ids from `Worker.sectionId`, and `DISPATCH_SYMBOLS` in the same order;
- `Leanux/Kernel/Decision.lean` constructors, `correspondence/kcov.json`'s
  function list and `OperandExclusion`: append-only blocks per stream;
- the fixture modes in `Env`/`Runner` (L's `bare`; W8's `foreignCreator`)
  and the routing model (W9 owns; W4's MTU and W5-W6's rules extend it;
  L's `routesViaWg0` is retired by W9's `route4/6`).

Not in this commit, by design: W5+W6's own interface step (its stream H,
above) and W8-G's per-trace arm subset on the wire are those streams'
first commits; `Leanux/Env/Stack.lean` and `Leanux/WG/PeerRemove.lean` are
created by the streams that own them.
