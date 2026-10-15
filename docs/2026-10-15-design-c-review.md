# Design C review: the IPv4 FIB trie — 2026-10-15 [AGENT, reviewer, Claude Opus 5.5]

Review of `docs/2026-10-15-design-c-fib-trie.md` at `task/design-c` 5c760b9
(from main ca6b22e). Method: every C line the note cites was read in
`.deps/linux` (6.12.110) against `kernel/config-x86_64-net-choice`; the two
probes were rerun read-only over the dump the note names
(`.worktrees/index-lookup-fix/.artifacts/check/20261014T184449Z`, 261 traces,
no trace in two chunks), and their output matches the note's tables. A
throwaway per-line query over the same dump (in `.tmp`, not committed)
settled the caller questions below. No boot, no check run. The checker's
semantics were read in `evaluator/check.py`, the allocation machinery in
`harness/steer.py`, the fixture in `harness/guest.c`.

The core of the note is right. The local-table aliasing (fib_frontend.c:50-71,
fib_trie.c:2390-2420, ip_fib.h:290-332), the key and index arithmetic
(fib_trie.c:214-229), the thresholds and `MAX_WORK` (:290-293, :804-911), the
lookup's three steps and backtrace (:1426-1629), the delete's
`FA_S_ACCESSED` flush (:1754-1755), the fixture's five routes, and the
transcribed shape (the probe reproduces positions 29, 26 and 22 that the
kernel records at the flush climb, `collapse` and `resize`) all hold.
`resize` belongs in scope: with `fib_trie.c` anchored, the walk's decisions
depend on the shape. The findings below are about what the note leaves
out, where it overstates what the instruments can settle, and how it
stages the work.

## Findings

### 1. Blocking: C1 leaves out callers of `fib_table_lookup` that run inside the window, and U1's cut of `__inet_dev_addr_type` cannot work

Once `fib_trie.c` is anchored in C1, every in-window call of a trie
function needs a mirror counterpart. Otherwise the check reports "Linux ran
a decision function the mirror reported nothing in", or an unreported
decision (check.py:1166-1176). The note lists three consumers in C1:
`send4`, the batch's `xmit` and `dst_mtu`. The kernel has more:

- `__inet_dev_addr_type` calls `fib_table_lookup` at fib_frontend.c:225
  inside the window in 14 traces (b1_basic, b1_other_endpoint,
  b1_trie_routing, b1_v6, l_delete_*, w4_set_mtu_0, w9_deladdr_then_send;
  lines 217-233 covered). One caller is on the path the note mirrors:
  `fib_del_ifaddr` uses its result to decide on `fib_sync_down_addr`
  (fib_frontend.c:1334-1343). Other callers are `fib_valid_prefsrc` inside
  `fib_create_info` (fib_semantics.c:1401-1405, reached by any
  prefix-route or broadcast insertion, so by the proposed `wg_addaddr`),
  `fib_check_nh` (:1173), `__inet_bind` (af_inet.c:493) and the ARP
  constructor (arp.c:242).
- `__ip_dev_find` falls back to a lookup in the local table when the source
  is not an interface address (devinet.c:160-172). That is the C's rule
  behind the mirror's "non-local source is `-ENETUNREACH`" and behind
  accepting `127.0.0.2`. Today it is covered only on the found-address arm
  (devinet.c:174, 118 traces), but the corpus can reach the fallback.
- `fib_compute_spec_dst` (121 traces) can run `fib_lookup` for a
  non-local route.

U1 proposes to cut `__inet_dev_addr_type` and `inet_addr_type_*` by name.
That hides their own lines, but not the `fib_table_lookup` decisions they
cause in an anchored file. Cutting a function on a mirrored path
(`fib_del_ifaddr`) also undeclares a decision whose outcome steers that
path.

Settle: list every in-window caller of `fib_table_lookup`, `_insert`,
`_delete` and `_flush` from the dump. The query is a frame-chain grep on
`coverage-map.json`. Make each caller a C1 consumer of the pure lookup,
mirrored unanchored if its file waits for C2, and drop those functions from
the cut list.

### 2. Blocking: C1 does not provide what campaign 3 needs, and the lookup is not pure

The note's summary and section 12 say campaign 3 needs both the output
route and the input route as mirrored code, with "the receive predicate's
local decision" as "one call of the same function on the namespace's
trie". The landing table puts the input sequence (rows 5 to 13 as
decisions) in C3. C1 alone therefore does not "unblock campaign 3's
composition", and the plan's critical path (C1 at about day 4) is wrong by
C2 plus C3.

The C lookup also writes. `fib_alias_accessed` sets `FA_S_ACCESSED` inside
step 3 (fib_trie.c:1571), before the error test. A "pure and total"
`tableLookup` returning only a result either drops that write, which breaks
mutant 6's rule and the `w9_*delroute_untouched` pair, or hides it in the
wrapper without saying so.

Settle:
- Write campaign 3's interface as a requirement. For example: lookup is
  `trie → flow → result × accessed-alias position`, and the wrapper
  applies the write.
- Either move the input sequence (or at least `fib_lookup` from
  `ip_route_input_slow` with the `RTN_LOCAL` and no-route arms) into C1,
  or restate that campaign 3's composition waits for C3 and correct the
  plan's row C and critical path.

### 3. Blocking for C2: hidden inputs the note misses, so "no hidden input" and "Oracle changes: none" do not hold as written

- (a) `dev_addr_genid` is a per-namespace counter seeded with
  `get_random_u32()` at namespace init (route.c:3665). `fib_result_prefsrc`
  compares it at fib_semantics.c:1383-1384 on every source selection
  through a nexthop without prefsrc. The dump shows 73 records with **43
  distinct random operand pairs in 43 traces** (`0x19107a3`,
  `0x1cd3269c`, ...). It is bumped at fib_frontend.c:1458, :1463 and :1505,
  and `nh_saddr_genid` caches it per nexthop (fib_semantics.c:1367). None
  of this is in 1.7, 3.1 or 5. The outcome is deterministic from a relative
  counter, but the operands need an `operand_exclusions` entry
  (kcov.json), and the counter and the per-nexthop cache need to be mirror
  state.
- (b) `net->hash_mix` is drawn by `get_random_bytes` at namespace creation
  (net_namespace.c:330, outside the window). It picks the
  `fib_info_devhash` bucket (fib_semantics.c:333) and the laddr hash bucket
  that `fib_sync_down_dev` (:2015-2021) and `fib_sync_down_addr` walk. Those
  are global tables shared by every namespace, with 256 devhash buckets. A
  random collision between wg0's bucket and another nexthop's (`lo` in the
  same namespace, the W8 park namespace, a namespace whose `cleanup_net`
  has not run) covers the `continue` arm at :2021. That arm is uncovered
  in this dump. Expect a spurious red in very roughly 1/256 of the down and
  delete traces once `fib_semantics.c` is anchored. Under AGENTS.md this is
  a hidden input that changes control flow: it must be recorded at its
  source, which is a record-only change (approved as a class, but then
  "Oracle changes: none" is false), or excluded with a stated reason.
- (c) `fib_info_cnt` and `fib_info_hash_size` are global across namespaces.
  The comparison at fib_semantics.c:1468 records `(0x10, 0x3)` in all 4
  in-window cases. Its operands depend on how many infos other namespaces
  hold at that moment, including a previous trace's namespace before its
  asynchronous `cleanup_net`. That makes it state the environment must pin
  with an exact rule (contended-host note), or an operand exclusion.

Settle: add a "hidden inputs of the route paths" subsection covering (a) to
(c), each with its treatment. Decide (b) before C2: record it or exclude it
with a reason.

### 4. Should-fix: the checker cannot settle the walk as the note claims; check the fixture's shape against `/proc/net/fib_trie`, not `RTM_GETROUTE`

Trie decisions repeat many times per operation, so they must be
`repeatable`. For those, `control_flow` checks the set of outcomes per
operation, and both outcomes reported waive the opposite-outcome test
(check.py:1019-1026, :1100-1106, :1141-1142). `operand_agreement` requires
only that each pair the mirror reports exists somewhere among the
operation's kernel rows. The guest deduplicates rows, and surplus kernel
rows are allowed (check.py:1236-1245). A mirror that takes fewer or
different steps but reports a subset of the kernel's pairs passes.

So the three claims in 9.2, 11 and 13.1 overstate what a run settles:
"checkable from the first build", "a mutant of the arithmetic is rejected
by the operand check, not only by the outcome", and "the first `wireguard`
suite run settles it". Mutant 1 shows the problem. At the pos-26 node,
every corpus destination `10.0.0.x` has `cindex = 2`, and
`cindex &= cindex - 1` equals 0 for any one-bit `cindex`. So
`cindex = 0` takes the same path and the same result, and mutant 1 most
likely survives. Mutant 2 (`slen > pos` dropped) can also leave results and
pair sets unchanged.

The note's fallback remedy, an `RTM_GETROUTE` dump, returns the routes, not
the shape. `/proc/net/fib_trie` prints every tnode's prefix, bits, full and
empty children counts, and each leaf's alias order (fib_trie.c:2785-2813;
`CONFIG_PROC_FS=y`).

Settle:
- Read `/proc/net/fib_trie` outside the window after the fixture's setup
  and after each operation that changes the table. Compare it with the
  mirror's trie as a new comparison class, with its one-off mutant, from
  C1. This is cheap and checks shape and counts exactly.
- Design corpus destinations where a wrong walk changes the result: a
  `cindex` with two bits set over a populated sibling, a more specific
  prefix under a stripped index.
- Rederive the mutant list against the existence and set semantics.

### 5. Should-fix: the alias order is wrong in the note

The leaf's list is sorted by `slen` **ascending** (longest prefix first),
then `tb_id` descending: `fib_insert_alias` stops at the first
`new->fa_slen < last->fa_slen` (fib_trie.c:1172-1177), and
`fib_find_alias` skips `fa_slen < slen` and stops at the first larger one
(:997-1004). Section 1.5 says "ordered by `slen` descending then `tb_id`
descending". The step-3 scan order and `fib_remove_alias`'s use of the last
alias for the leaf's `slen` (:1654-1660) depend on this.

Also in 1.6: an alias is skipped when the key differs *above* its suffix,
in its prefix bits (:1561), not "within its suffix".

Settle: correct 1.5 and 1.6. A transcription in the C1 unit test will catch
the rest.

### 6. Should-fix: the `rt_cache_flush` sites are not only `fib_*`'s, and the aliased tables affect the flush

The note replaces the six generation bumps with "the C's own
`rt_cache_flush` sites", but lists only fib_frontend.c and fib_trie.c.
Other sites that run here:

- `ip_rt_multicast_event` (route.c:3445-3447), from igmp.c:1484 when a
  device joins all-hosts at `ip_mc_up`. It is covered in 189 traces.
- nexthop.c:3886 on `NETDEV_CHANGEMTU`. With fib_frontend.c:1521, a
  changed MTU flushes twice.
- arp.c:1332 (`NETDEV_CHANGEADDR`) and the devinet sysctl flushes
  (devinet.c:2421-2509).

Once route.c is anchored (C3), `rt_cache_valid:1605` and `rt_is_expired`
(:399) compare the **absolute** `rt_genid`; the dump has values up to
`0x11`. The mirror must then count every flush since the namespace was
created, including the fixture's setup, or exclude the operands.

Two related points are missing from 1.5 and 1.8. `fib_flush` walks the
table hash, so it runs `fib_table_flush` twice over the one aliased trie,
MAIN (index 254) then LOCAL (255), each pass resizing on the way up
(fib_frontend.c:189-195). And `fib_disable_ip` ends with `arp_ifdown`
(:1443).

Settle: enumerate every flush caller reached, from the dump. State the
two-pass flush and the generation's operand treatment.

### 7. Should-fix: dropping the parent pointer is not free; `replace` and `update_children` are missing

`update_children` branches on parent identity: `node_parent(inode) == tn`
(fib_trie.c:462). The operands are kernel pointers, and the outcome
distinguishes nodes `inflate` and `halve` just created (parent already set)
from moved children. `replace` (:508-533) runs it, frees the old node, and
then calls `resize` recursively on every full child (:526-531). Section 1.4
mentions neither, and the claim that an explicit path stack carries "what
the parent pointer gives `resize`" misses both. Nothing exercises them
today; the proposed insertion corpus will.

Settle: add `replace` and `update_children` to 1.4 and section 8. Track a
"created in this step" mark (or equivalent) so the mirror reproduces :462,
declared without operands.

### 8. Should-fix: U1 runs into functions IPv4 and IPv6 share, and it revises a user decision

- `fib_semantics.c` holds helpers IPv6 calls inside the window:
  `fib_nh_common_init` (185 traces, from `fib6_nh_init`,
  net/ipv6/route.c:3675, at every `wg_up`), `fib_nexthop_info` (189
  traces, from `rt6_fill_node`, :5670 and :5841), and
  `fib_nh_common_release`. Function-granular `functions` and `helper_cuts`
  lists cannot mirror one of these for IPv4 and cut it for IPv6. Either
  the IPv6 calls go red ("a decision function the mirror reported nothing
  in") or the IPv4 decisions go undeclared. The cut counts "7, 12 and 15"
  do not cover this.
- route.c sits under the [USER 2026-10-07] boundary decision
  (decisions.md:79-87; census line 461: "reached only where WireGuard's
  observables depend on it"). The input corpus's `-EHOSTUNREACH` and
  `ip_error` path reverses the [AGENT 2026-10-08] deferral of `ip_error`
  (decisions.md:107-111). U1 should say it revises the first and the
  design should record the second.

Settle: propose a mechanism for shared helpers before U1, such as a
per-caller cut keyed on the outer frame (an instrument change with its
one-off mutant) or keeping `fib_semantics.c` unanchored. Restate U1 with
the provenance.

### 9. Should-fix: the allocation site list is wrong and incomplete

- Wrong lines: `tnode_alloc` is `kzalloc` at :333 and `vzalloc` at :335,
  not :328 and :330. The `vzalloc` arm is not a slab call, so the kind-305
  hook cannot arm it; it is reachable only above 511 children. The alias
  allocations are at :1281 and :1344, not :1274 and :1335.
- Missing: `ip_fib_metrics_init`'s `kzalloc` (net/ipv4/metrics.c:76),
  reached by every W4 route insert with `RTAX_MTU`.
- Missing: `fib_nh_common_init`'s `alloc_percpu_gfp`
  (fib_semantics.c:621). Percpu allocations were retired as lax and
  unsteerable for `dstCacheInit` (docs/2026-10-05-a-alloc.md:102); the
  same treatment must be stated here.
- Allocations already happen inside the window today: in the four
  `fib_table_insert` traces, `fib_create_info` allocates the info and its
  percpu array and then frees them when `fib_find_info` finds the shared
  one (fib_trie.c:1218 runs before the `-EEXIST` test at :1243).

Settle: correct section 5, and give each site its class and treatment.

### 10. Should-fix: the input side is incomplete and one corpus item cannot work

- "A decrypted packet to `127.255.255.255` (broadcast, `brd_input`)" never
  reaches `fib_lookup`. A loopback destination is a martian at
  route.c:2316-2318 (`route_localnet` 0).
- Row 10 (limited broadcast) goes to `brd_input` (:2301-2302), passes
  `fib_validate_source`, and is delivered by udp.c's broadcast path, which
  is outside this module. Rows 11a-c are `ip_route_input_rcu`'s multicast
  branch (:2493 onward), not `ip_route_input_slow`.
- Missing from 1.9:
  - `!in_dev` (:2282), the MTU-below-68 state of the `w4_set_mtu_0`
    traces;
  - early demux (ip_input.c:334-352), which runs before any input route;
  - `fib_has_custom_local_routes`, set by any `RTN_LOCAL` route added over
    rtnetlink (fib_frontend.c:918-919, a possible `wg_addroute` case). It
    moves `fib_validate_source` from the fast path to
    `__fib_validate_source` (:436-438, :451), which the note leaves out of
    scope, so it must be a fail-noisy outcome.

Settle: rewrite rows 5 to 13 against the C's actual order and functions.
Mark which rows become decisions and which stay exclusions at a new site.
Fix the corpus item, using a non-loopback broadcast address after
`wg_addaddr` with a prefix shorter than 31.

### 11. Should-fix: harness work is not costed, and ten agent-days is not credible

The corpus needs:
- new guest operations: `wg_addroute` with flags, metric and MTU, and
  `wg_addaddr`;
- a generalised `wg_delroute`;
- new trace fields and the generator class.

The plan expects the design to say what the guest must add
(wireguard-parallel-plan.md:110-112); the note does not, and C1's four days
include none of it.

The estimate also has to absorb findings 1 to 10:
- more consumers in C1;
- a shape oracle;
- hidden-input treatment;
- `replace` and `update_children`;
- the shared-helper mechanism;
- three anchored files whose cut lists cannot be counted before the first
  red run.

My estimate is 15 to 20 agent-days, with C1 at 6 to 8 including the harness
operations. The proof carry is separate.

Settle: a C1 task list with the harness items, re-estimated after findings
1 to 3 are settled.

### 12. Note: the proof carry is plausible but different in kind

With the accessed bit in `Kernel`, every `send4`, batch `xmit` and input
lookup writes kernel state where today it writes `World`
(`defaultRoute4Accessed`). Frames of the form "this path leaves `Kernel`
unchanged except ..." change in kind, not just in location. On
`proofs/campaign`, `SocketSend4.lean` names the routing environment 15
times.

The counts in 12 match at the commits the note names: 6 files on main
including `Logged/Syscalls.lean`'s `routeIntoWg0`, and 18 or more on
b1ec9e8. Both campaign branches have moved since (now 36e8a44 and
e74f3ca). The two days for campaign 1 is a guess I cannot confirm without
the change.

The representation `Array (Option KeyVector)` is a nested inductive. That
matches the C, but recursion and induction over it cost more in Lean than
over a binary tree. Section 12 should name that cost.

### 13. Note: the probe figures support the tables, with small corrections

The rerun reproduces 9.1 and 9.2 exactly. Corrections:
- The four `fib_table_insert` traces are l_down_after_session,
  l_down_up_keepalive, l_down_up_stale_response and l_up_down_noop, not
  "the four `l_down_up_*`".
- For `10.0.0.x` the backtrace strips `cindex` from 2 to 0 inside the
  pos-26 node and does not climb (:1522 is evaluated, its body is not
  entered).
- The 9.3 table and the probe's labels cite fib_frontend.c :1150-1153 and
  :1155-1157 for the `/8` and broadcast routes. The C has :1155-1158 and
  :1161-1164, as section 1.8 itself says.
- In section 8, the flush's null and tnode tests are at :2041 and :2044.
- `fib_select_default` (fib_semantics.c:2070) has decisions of its own that
  the tie corpus reaches. With aliases that have no gateway it skips each
  candidate, and it reads neighbour state (`fib_detect_death`) only for
  gateways. Add it to section 8.
- The `&& max_work` terms at :869 and :892 cannot be witnessed at corpus
  scale: ten successive inflates need about 2^10 children. Say "declared,
  unwitnessed".
- The dump sits in a worktree slated for cleanup. A rerun is
  `capped -- scripts/in-bundle python3 -m evaluator.check --suite wireguard`
  on s4, about 3 minutes.

### 14. Note: deferring IPv6 is justified; the composition must be scoped to IPv4

Cost against payoff is a fair reason, and no charter result needs the IPv6
trie. But campaign 3's end-to-end routing composition must then be stated
for IPv4 only, in its charter. The IPv6 route insertions inside the window
at `wg_up` are part of finding 8's problem.

### 15. Note: U4 changes a standing rule

The "mirror carries no theorem" rule in AGENTS.md lists the mirror's
directories (`FS`, `WG`, `Kernel`, `Env`, `Runner.lean`; `Seccomp` is
already absent from that list). A new `Leanux/Net/` tree is a
standing-rule edit to put to the user, and `scripts/proof-gate`'s
import check should cover it.

## Verdict

**Build with the named changes.** The architecture stands:
- the trie as a mirror module of the C's shape, with `resize` whole;
- the fixture's trie built by the mirror's own insert in the fixture's
  order (sound: each trace starts in a fresh namespace, guest.c:751);
- no kernel change for the trie itself.

Before the build starts, the note needs:
- the C1 consumer set covering every in-window caller of the trie
  (finding 1);
- campaign 3's interface stated, with the input route staged accordingly
  and the accessed-bit write made explicit (finding 2);
- the hidden inputs of the route paths treated, with `hash_mix` decided
  before C2 (finding 3).

Findings 4 to 11 change the shape oracle, the facts in 1.4 to 1.9, the
anchoring mechanism and the estimate. They belong in the revised note or
C1's plan. No redesign is needed, but the schedule moves: C1 is not a
four-day unblocker for campaign 3 as written.
