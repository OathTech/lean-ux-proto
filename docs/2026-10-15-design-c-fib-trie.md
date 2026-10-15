# Design C: the IPv4 FIB trie as a mirror module — 2026-10-14 [AGENT, fork of the coordinator]

Lane C of [the parallel plan](2026-10-14-wireguard-parallel-plan.md):
`net/ipv4/fib_trie.c` as a new mirror module with its own corpus, record-only
hooks if any, frames only for the proofs. It is the plan's critical path:
campaign 3's end-to-end routing composition needs the output route and the
input route to be mirrored code with a contract boundary, not the
environment's summary. Read-only against Linux 6.12.110 (`.deps/linux`) and
the s4 oracle (identity `6b2018b9`); the mirror at main ca6b22e. No
implementation. Sections 2 and 9 are measured; everything else is the C
verified by line.

Summary. The fixture's routing is one small LC-trie: four internal nodes
and five leaves after boot (section 9), shared by the local and main
tables on this configuration. Its lookups run inside the coverage window
in 183 of 261 WireGuard traces, with the backtrace in 56 and the
no-route miss in 10, and every decision of the lookup, the delete, the
flush and the resize already lands in the comparison stream with its
operands, so the module needs no kernel change: no hook, no record kind.
What the window never contains is an insertion of a node: the boot-time
and `route_into_wg0` inserts run before or after the per-operation
capture, so the mirror constructs the trie from the C's rules and the
corpus adds route insertions inside the window. The module replaces the
environment's six hand-written generation bumps and its two-case route
function with the C's own `rt_cache_flush` sites and `fib_table_lookup`.
IPv6 is deferred to its own lane with the reason in section 7. Estimate:
about ten agent-days in three landings (section 13); the first, the trie
proper, is what campaign 3 waits for.

## 1. The C, verified

Configuration (`kernel/config-x86_64-net-choice`): `CONFIG_IP_ADVANCED_ROUTER`
unset, hence `CONFIG_IP_MULTIPLE_TABLES` unset; `CONFIG_IP_FIB_TRIE_STATS`
unset; `CONFIG_IP_ROUTE_MULTIPATH` unset; `CONFIG_IPV6=y` with
`CONFIG_IPV6_MULTIPLE_TABLES` unset.

### 1.1 One trie for two tables

Without `IP_MULTIPLE_TABLES`, `fib4_rules_init` (fib_frontend.c:50-71)
creates the main table and then the local table as an *alias* of it:
`fib_trie_table(RT_TABLE_LOCAL, main_table)` (fib_trie.c:2390-2420) shares
`tb_data`, so both tables are one `struct trie` whose aliases are told
apart by `fa->tb_id`. `fib_get_table`/`fib_new_table` are the inline
versions in `include/net/ip_fib.h` (the `#ifndef CONFIG_IP_MULTIPLE_TABLES`
block): `fib_lookup` (ip_fib.h:314-328) looks the main table up once and
maps `-EAGAIN` to `-ENETUNREACH`.

### 1.2 The structure (fib_trie.c:112-291)

`t_key` is a 32-bit host-order key. A `key_vector` has `key`, `pos`, `bits`,
`slen` and either an alias list (`bits == 0`, a leaf) or a child array of
`1 << bits` pointers (a tnode); the enclosing `tnode` carries
`empty_children`, `full_children` and the parent pointer (:120-137). The
root (`t->kv`) has `pos = KEYLENGTH` and `IS_TRIE` tests that (:117, :2411).
A node's significant bits are those above `pos + bits`; the `bits` bits at
`pos` index the children; `slen` is the longest suffix length below the
node, which bounds how far a lookup must backtrack. `get_cindex` is
`(key ^ kv->key) >> kv->pos` (:219); `get_index` the same with the root
special case (:221-229). `child_length` is `(1 << bits) & ~1` (:214-217).
Thresholds: `halve_threshold 25`, `inflate_threshold 50`, and the root's
`15`/`30` (:290-293).

### 1.3 Allocation and children (fib_trie.c:309-535)

`tnode_alloc` is `kzalloc(GFP_KERNEL)` up to a page, `vzalloc` above
(:320-336, the calls at :333 and :335). `leaf_new` is `kmem_cache_alloc(trie_leaf_kmem, GFP_KERNEL)`
(:354-375), `tnode_new` sets the key to its significant bits and `slen =
pos` (:377-401). `put_child` maintains the empty and full counts and raises
the parent's `slen` (:418-444); `tnode_full` is "an internal child with no
skipped bits" (:407-413). Frees are `call_rcu` (:309-317) and `tnode_free`
calls `synchronize_net` once `tnode_free_size` passes
`sysctl_fib_sync_mem` (:490-506): neither has an observable.

### 1.4 Resize (fib_trie.c:537-911)

`inflate` doubles a node's child array (`pos - 1`, `bits + 1`), splitting
full children into two half nodes and lifting the others (:537-630);
`halve` does the reverse (:633-686); `collapse` removes a node with one
child or none (:688-707); `update_suffix` recomputes `slen` by a strided
scan (:709-743). `should_inflate` is `used > 1 && tn->pos && 50 * used >=
threshold` with `used = child_length - empty + full` and the root's
threshold (:804-817); `should_halve` is `used > 1 && bits > 1 && 100 * used
< threshold` (:819-831); `should_collapse` is `used < 2` (:833-845, the `KEYLENGTH` term at :840-841).
`resize` inflates while it should (at most `MAX_WORK` 10 steps), returns
if it inflated at all, else halves while it should, then collapses
(:847-911); on an allocation failure a step is skipped and the loop
breaks (:871-877, :894-900). `trie_rebalance` resizes up to the root
(:1104-1108).

### 1.5 Find, insert, delete, flush

`fib_find_node` descends by `get_cindex` until a leaf (:971) or a null
child (:946) or a mismatch (`index >= 1 << bits`, :965) and returns the
parent (:936-973). `fib_find_alias`
walks a leaf's list, ordered by `slen` descending then `tb_id`
descending, and returns the first alias at `(slen, tb_id)` whose DSCP and
priority fit, or the insertion point (:983-1013). `fib_insert_node`
allocates the leaf, and if the slot is taken (:1128) creates a one-bit
tnode at `__fls(key ^ n->key)` holding both, pushes the suffix and
rebalances (:1110-1158). `fib_insert_alias` places the alias in its leaf by `slen`
and `tb_id` (:1160-1194, the suffix update at :1188). `fib_table_insert` (:1200-1398): `fib_create_info`
first (shared infos, 1.7); an existing alias with the same DSCP and
priority is `-EEXIST` under `NLM_F_EXCL` (:1243), replaced under
`NLM_F_REPLACE` (:1269-1324, the new alias allocated at :1281, with
`rt_cache_flush` only if the old alias was accessed, :1321-1322), or
appended (:1330-1335); `NLM_F_CREATE` is required for a new one (:1339),
allocated at :1344 and inserted at :1360; a prefix of length 0 counts
`tb_num_default` (:1382-1383); then `rt_cache_flush` unconditionally
(:1385). `fib_table_delete`
(:1694-1759) finds the leaf and the alias (`-ESRCH` at :1708-1709 and
:1713-1714), matches type, scope, prefsrc, protocol, nexthop and metrics
(:1721-1743), notifies, decrements `tb_num_default` for a default
(:1749-1750), removes the alias (`fib_remove_alias`, :1632-1661: frees an
emptied leaf (:1645) and rebalances, else pulls the suffix), flushes the
cache only if `FA_S_ACCESSED` (:1754-1755), and releases the info. `fib_table_flush` (:2006-2096) walks the trie in reverse, deletes the
aliases whose info is `RTNH_F_DEAD` (or everything with `flush_all`),
updating suffixes and resizing each node on the way up.

### 1.6 Lookup (fib_trie.c:1401-1630)

`prefix_mismatch` is `(key ^ prefix) & (prefix | -prefix)` (:1401-1406).
`fib_table_lookup` with `key = ntohl(daddr)`: an empty trie returns
`-EAGAIN` (:1442-1446). Step 1 descends by `get_cindex`, breaking on a
skip-bit mismatch (:1470) or a leaf (:1474), recording `pn`/`cindex` only
at nodes with `slen > pos` (:1480-1483), and goes to backtrace on a null
child (:1486-1487). Step 2 backtracks: at a node whose prefix mismatches or
whose `slen == pos` it strips the lowest set bit of `cindex`
(:1499, :1543) and climbs when `cindex` is 0 (:1522-1540), returning
`-EAGAIN` at the root (:1529-1532). Step 3 scans the leaf's aliases: an
alias is skipped if the key differs within its suffix (:1561-1562), on a
DSCP mismatch (:1564), a dead info (:1567), a scope narrower than the
flow's (:1569); then `fib_alias_accessed` sets `FA_S_ACCESSED` (:1571), an
error type returns its error (:1573-1579), a dead-flagged info is skipped
(:1581), and the first nexthop that passes `fib_lookup_good_nhc` (dead,
linkdown, `oif`; :1409-1423) fills the result after the `NOREF` test
(:1603): prefix, prefix length, nexthop, type, scope, DSCP, info, table,
alias head (:1606-1616). A leaf
with no usable alias falls back to the backtrace (:1621-1629).

### 1.7 fib_info (fib_semantics.c)

`fib_create_info` (:1415-1660) validates type, scope and flags, allocates
the info (`kzalloc`, :1489; the info hash may grow by `kvzalloc`,
:1468-1486), copies protocol, scope, flags, priority, prefsrc, type and
table, initialises the one nexthop (`fib_nh_init`, :652), and for
`RT_SCOPE_HOST` takes the device by `oif` with `fib_nh_scope =
RT_SCOPE_NOWHERE` (:1562-1584), else runs `fib_check_nh` (:1585-1597);
`fib_valid_prefsrc` (:1599-1602); `fib_info_update_nhc_saddr` picks the
nexthop's source by `inet_select_addr` (:1603-1611); then `fib_find_info`
returns an identical existing info with `fib_treeref` incremented
(:1615-1621; the comparison at :409-437 is protocol, scope, prefsrc,
priority, type, table, metrics, flags and nexthop), else the new one is
hashed and linked to its device bucket (:1622-1649). `fib_release_info`
unhashes at the last tree reference and marks `fib_dead` (:261-284).
`fib_sync_down_dev` marks every nexthop on the device dead or linkdown
and counts the infos that went fully dead (:2004-2068); `fib_flush` then
removes their aliases (fib_frontend.c:184-197). `fib_select_path` with a
single path only chooses a source when the flow has none
(`fib_result_prefsrc`, :2269-2297), and `fib_select_default` runs only with
`tb_num_default > 1` (:2282-2284, :2070). `fib_props` (:99-147) maps types
to errors and minimum scopes.

### 1.8 What a device's address adds (fib_frontend.c:1083-1343)

`fib_magic` builds a `RTPROT_KERNEL` config with the address as prefsrc
and the device as `oif`, `NLM_F_CREATE | NLM_F_APPEND`, table LOCAL for
local and broadcast types and MAIN for unicast, scope HOST for local
types else LINK, and inserts or deletes (:1083-1121). `fib_add_ifaddr`
adds the `/32` local route of the address (:1140), and if the device is up
(:1142) the explicit broadcast (:1146-1150), the prefix route for a prefix
shorter than 32 (local on a loopback device, unicast otherwise;
:1152-1159) and the network broadcast for a prefix shorter than 31
(:1161-1164).
`fib_del_ifaddr` removes them, keeping those another address still
justifies (:1197-1343). The notifiers: `NETDEV_UP` of an address or a
device adds, `NETDEV_DOWN` of the last address disables IP on the device
(`fib_disable_ip`: `fib_sync_down_dev` and `fib_flush`, :1436-1444,
:1461-1469), a device's `NETDEV_DOWN` disables without force, and
`NETDEV_CHANGEMTU` runs `fib_sync_mtu` and `rt_cache_flush` (:1477-1530).
The loopback gets `127.0.0.1/8` at its `NETDEV_UP` (devinet.c:1601-1613).

### 1.9 From the trie to a route (route.c)

Output: `ip_route_output_key_hash_rcu` (:2696-2864) rejects a multicast,
limited-broadcast or zeronet source with `-EINVAL` (:2706-2712), a source
that is not a local address with `-ENETUNREACH` (:2714, :2751-2754), takes
the loopback for an empty destination (:2788-2795), calls `fib_lookup`
(:2799), returns its error unless an `oif` was given (:2800-2830), takes
the local route with the prefsrc or the destination as source
(:2833-2841), else `fib_select_path` and the result's device (:2855-2857),
and builds the route in `__mkroute_output` (:2545-2665): the per-nexthop
cached route is reused when `rt_cache_valid` (:2633-2634), else
`rt_dst_alloc` (`dst_alloc`, a `GFP_ATOMIC` allocation, :1668-1693) and
`rt_set_nexthop` with the info's metrics (:1609-1660). Input:
`ip_route_input_slow` (:2265-2477) drops martian sources and destinations
(:2296-2321), calls `fib_lookup` (:2347), maps a miss to `-EHOSTUNREACH`
with forwarding off (:2348-2352), delivers a `RTN_LOCAL` result after
`fib_validate_source` (:2363-2368), refuses to forward (:2371-2373), and
builds the input route (:2396-2443). `fib_validate_source`'s fast path on
this configuration (`rp_filter 0`, `accept_local 0`, no custom local
routes) is `inet_lookup_ifaddr_rcu(src)`: a local source is `-EINVAL`,
anything else passes with no trie lookup (fib_frontend.c:421-451).
`rt_cache_flush` is `rt_genid_bump_ipv4` (:406-409); `rt_cache_valid` and
`ipv4_dst_check` compare a route's generation with the namespace's
(:1602-1607, :1245-1248).

## 2. What the mirror represents today, versus the C

The environment (W9, [the netns and routing design](2026-10-06-w8-w9-netns-routing.md)
2.6 and 4.2) holds `World.addrs4/addrs6`, `defaultRoute4/6`,
`defaultRoute4Accessed`, `ipv4Gen/ipv6Gen`, `routesPending` and the W4
`routes` list (`Leanux/Kernel/Defs.lean:1572-1599`), and answers
`World.route4` by three cases: a non-local source is `-ENETUNREACH`, a
`127/8` or wg0 destination is the loopback with the prefsrc rule, anything
else the default route via wg0 while it exists (:1670-1709). The
generation moves at six hand-written sites (`Env.lean:585-603`, `:618`,
`:642`, `:657`, `:672-673`, `:676`), one of which reproduces the
`FA_S_ACCESSED` rule of `fib_table_delete`. `send4`/`send6`
(`Leanux/WG/Socket.lean:203-278`) consume the route through `routeLookup`
with the dst cache keyed on the generation; the batch's `xmit` routes the
sender's datagram the same way (`Env.lean:913`); the input side is the
receive predicate's exclusion rows (`Leanux/Env/Stack.lean:117-130`): a
destination other than wg0's address is `excluded` (row 13), a source
equal to it `excluded` (row 12). The route's MTU is the W4 list
(`Env/IpStack.lean:172-174`).

Against the C, this is a correct summary of the fixture's tables for the
five destinations the corpus uses, and it is exactly what the plan calls
the environment's summary: no node, no alias, no info, no lookup walk, no
insertion, and the generation rule copied by hand. The census row for
`net/ipv4/route.c` says "reached only where WireGuard's observables depend
on it, as hidden inputs or observations" (`2026-10-13-decision-census.md:461`);
`net/core/dst_cache.c` is not anchored (item 8).

## 3. The module's scope at the thin layer

### 3.1 State, the C's shape

`Leanux/Net/Fib/Types.lean` (a new `Leanux/Net/` tree; decision U4):

- `KeyVector`: an inductive, `leaf (key : UInt32) (slen : Nat) (aliases :
  List FibAlias)` or `tnode (key : UInt32) (pos bits slen : Nat)
  (children : Array (Option KeyVector)) (emptyChildren fullChildren :
  Nat)`, with the root as the C's `pos = 32` node holding one child. The
  parent pointer is not represented: the walks keep their path as an
  explicit stack, which is the C's data flow (what the parent pointer
  gives `resize`, `node_pull_suffix` and the backtrace) without its
  memory. The counts are kept as data, not recomputed, because
  `should_inflate`/`should_halve` compare them and the comparison's
  operands are checked.
- `FibAlias`: `slen`, `tbId`, `dscp`, `type`, `state` (the `FA_S_ACCESSED`
  bit), `info : FibInfoId`, `fa_default`.
- `FibInfo`: `protocol`, `scope`, `flags` (`RTNH_F_DEAD`/`LINKDOWN`),
  `priority`, `prefsrc`, `type`, `tbId`, `metrics` (the `RTAX_MTU` the W4
  routes carry), `dead`, `treeref`, and one nexthop: `oif`, `dev`,
  `nhScope`, `nhFlags`, `nhSaddr`, `gwFamily` (always none here). Kept in
  `Kernel.fibInfos : TreeMap FibInfoId FibInfo` with the sharing of
  `fib_find_info` as the C's identity rule: the fixture shares the
  `127.0.0.1/32` and `127.0.0.0/8` local routes' info (same protocol,
  scope, prefsrc, priority, type, table, metrics and nexthop), so a
  `fib_release_info` of one leaves the other's reference.
- `FibTable`: `tbId`, `numDefault`, and the trie; the local table an
  alias of the main as in 1.1: one `Kernel.fib4 : FibTrie` per namespace
  (the W8 foreign-creator mode has two namespaces; B2 adds a third device
  state: the table lives beside the namespace's other per-net state).

The address lists stay the environment's (`World.addrs4`), since
`in_device` and `inet_select_addr` are devinet.c, outside the lane; the
module consumes them where the C does (`inet_select_addr`,
`inet_lookup_ifaddr_rcu`, `__ip_dev_find`).

### 3.2 Functions, the C's control flow

`Leanux/Net/Fib/Trie.lean`, each with its decisions declared in
`fib_trie.c` (section 8):

- the pure core: `findNode`, `findAlias`, `insertNode`, `insertAlias`,
  `removeAlias`, `resize` with `inflate`, `halve`, `collapse`,
  `updateSuffix`, `pushSuffix`, `pullSuffix`, `trieRebalance`, and
  `tableLookup` with its three steps, as total functions over
  `KeyVector`; a thin monadic wrapper reports each C choice point in
  order with its operands (`branchCmp` for `index >= 1 << bits`, the
  thresholds, `slen` comparisons) and consumes the allocation outcomes;
- `tableInsert`, `tableDelete`, `tableFlush` as the C's sequences over
  `fib_create_info`, `fib_find_info`, `fib_release_info`,
  `fib_sync_down_dev` (`Leanux/Net/Fib/Semantics.lean`), with the
  `rt_cache_flush` calls at the C's sites: these replace the six
  generation bumps of the environment, and `defaultRoute4Accessed` by
  the alias's own `FA_S_ACCESSED`;
- the entry points the fixture reaches (`Leanux/Net/Fib/Frontend.lean`):
  `fibMagic`, `fibAddIfaddr`, `fibDelIfaddr`, `fibDisableIp`, `fibFlush`,
  the `fib_inetaddr_event` and `fib_netdev_event` arms for `NETDEV_UP`,
  `NETDEV_DOWN`, `NETDEV_UNREGISTER` and `NETDEV_CHANGEMTU`, `fibValidateSource`'s
  fast path, `rtmToFibConfig` and `inetRtmDelroute`/`inetRtmNewroute`
  for the corpus's route operations;
- the consumers (`Leanux/Net/Route.lean`): `ipRouteOutputKeyHash`'s
  decision sequence down to the result `{dev, src, type, mtu}` consumed
  by `send4`, the batch's `xmit` and `wg_xmit`'s `dst_mtu`; and
  `ipRouteInputSlow`'s decision sequence to the `RTN_LOCAL` delivery,
  the `-EHOSTUNREACH` drop and the martian drops, consumed by the receive
  predicate in place of rows 5 to 13.

Environment rules that move into the mirror: `World.route4`, the six
generation bumps, `routeIntoWg0`'s and `wgDown`/`wgDelete`/`wgDeladdr`/
`wgDelroute`'s table edits (they become the C's notifier and rtnetlink
sequences on the trie), the receive rows 5 to 13 for IPv4. Rules that
stay: `routesPending` and its timing (the fixture's order, 14.3b of the
W9 design); the address lists; the W4 `routes` list as the source of the
fixture's `RTM_NEWROUTE` requests (now inserted into the trie with their
`RTAX_MTU`, so `dst_mtu` reads the alias's info instead of the list); the
dst cache; `World.route6` and everything IPv6 (section 7); the per-nexthop
route cache and `rt_dst_alloc` (3.4).

### 3.3 `resize` is in scope

Measured (section 9): the fixture's tables inflate three times at setup,
outside every window, and never halve; `collapse` runs on every deletion
and flush inside the window (19 traces). `inflate`/`halve` are reachable
by the corpus's route insertions and deletions (section 10: eight host
routes under one `/24` inflate the pos-22 node to four bits and their
deletion halves it), the thresholds' comparisons are recorded with
operands at `resize`'s sites, and the loop's structure is the C's data
flow on every deletion path. No profound reason excludes it; it is in
scope whole, `MAX_WORK` included. Only `tnode_free`'s `synchronize_net`
threshold and the `call_rcu` frees are cuts (no observable).

### 3.4 Cuts and the boundary below

Below the module: `dst_alloc`/`rt_dst_alloc` and the per-nexthop cached
route (`nhc_pcpu_rth_output`, `rt_cache_route`, `find_exception`,
`rt_add_uncached_list`): a hit or a miss there changes no observable the
mirror reads, only whether an allocation runs, and the allocation is a
cut helper range already (`ALLOC_HELPER_FILES`). `ipv4_mtu` reads the
route's metrics; the mirror reads the alias's info. `fib_info_hashfn`'s
bucket has no observable (`fib_find_info` compares the full identity).
`rtmsg_fib`, `fib_dump_info`, `fib_nlmsg_size`, `call_fib_entry_notifiers`
and `call_fib_nh_notifiers` are the netlink notifications and the
notifier chain: below the cut, as every rtnetlink notification is. The
`trace_fib_table_lookup` tracepoints are compiled no-ops here.

## 4. The observation boundary

What WireGuard's paths and observables depend on, each with its consumer:

| Observation | C | Consumer in the mirror |
| --- | --- | --- |
| the output route of a peer's endpoint: device, source, error | `ip_route_output_flow` → `fib_lookup` → `fib_select_path`/`fib_result_prefsrc` | `send4` (socket.c:48-80), the dst cache's fill, `SentDatagram.src` |
| `dst_mtu` of the route into wg0 | `rt_set_nexthop`'s metrics from the alias's info | `wg_xmit` (device.c:173), the batch's `xmitPackets` |
| the sender's inner route (does the datagram enter wg0?) | the same lookup with `saddr = 0` | the batch's `xmit` and `wg_xmit`'s entry |
| the decrypted packet's input route: local, unreachable, martian | `ip_route_input_slow` → `fib_lookup`, `fib_validate_source` | the receive predicate rows 5 to 13 |
| the route generation the dst cache checks | `rt_cache_flush` at the insert, delete, notifier and flush sites | `dstCacheGet`'s generation test |
| `-ENETUNREACH` with no default route; `-ESRCH`, `-EADDRNOTAVAIL`, `-EEXIST` of the route operations | `fib_lookup`'s `-EAGAIN` mapping; `fib_table_delete`, `fib_table_insert` | the W9 operations' results |

Not depended on and not modelled: the route's `rt_iif`, `rt_uses_gateway`,
the uncached list, the input route cache, the per-cpu output cache.

## 5. Records and hidden inputs

The trie has no hidden input of its own: no clock, no random draw, no
dispatch. Verified: `fib_table_lookup`, `fib_table_insert`,
`fib_table_delete`, `fib_table_flush`, `resize` and their helpers read
only the trie, the flow and the config; `fib_create_info` reads the
address lists and the device table; `fib_info_hashfn` has no seed. The
only hidden inputs are allocation outcomes, all `GFP_KERNEL` in task
context (class b-task, [the allocation design](2026-10-05-a-alloc.md)):
`leaf_new` (fib_trie.c:359), `tnode_alloc` (:328, :330), the alias
allocations (:1274, :1335), `fib_create_info`'s `kzalloc` (fib_semantics.c:1489)
and the hash growth (:1477-1478). They become `AllocSite` entries
(`.exact 1`), which is harness-side: the kind-305 hook is generic in
`slab_alloc_node` and records a site when its address is in the armed set
the guest loads (`gen-choice-stream.py:1466-1495`, `harness/steer.py:342-362`);
no kernel change. Their failure arms are modelled as the C's (`-ENOMEM`,
the `resize` step skipped) and reachable only when armed; the armed set
is per trace and the 64-range limit (`KCOV_ALLOC_RANGES_MAX`) is not
approached (seven new sites). `rt_dst_alloc` is `GFP_ATOMIC` and stays
below the cut (3.4).

Oracle changes: none. No hook, no record kind, no steering change, no
config change. The lane lands on s4.

## 6. Anchoring

`net/ipv4/fib_trie.c` is anchored in `correspondence/kcov.json` with every
reached function listed (the 26 of section 9, of which `fib_free_table`
and `fib_proc_exit` are the namespace exit's, cut with a note as the W8
teardown is) and the dump functions listed as unreached. For
`fib_frontend.c`, `fib_semantics.c` and `route.c` the choice is U1: anchor
them too, listing the reached functions the module mirrors and cutting
the rest by name (`__inet_dev_addr_type` and `inet_addr_type_*`, reached
in 189 traces by the socket layer's address classification;
`fib_compute_spec_dst`, by the sender's `IP_PKTINFO`; the notification
builders; the proc and sysctl exits; `__ip_select_ident` and
`ip_idents_reserve`, already the cut sites 20 and 21), about 10, 15 and
15 functions mirrored and 7, 12 and 15 cut; or leave them "mirrored but
unanchored" as B3 proposes for `timer.c`, with the module's control flow
in those files undeclared. The first is the thin-layer rule as written
(a mirrored choice point is a declared decision) and costs the cut list;
the second defers it. The note recommends the first, in the third landing
(section 13), with `fib_trie.c` anchored in the first.

## 7. IPv6

Deferred to its own lane. `net/ipv6/ip6_fib.c` (2,797 lines) is a different
structure (a radix tree of `fib6_node` with `rt6_info` leaves, subtree
pointers, a serial number per table) and `net/ipv6/route.c` (6,887 lines)
a different consumer; nothing of the IPv4 module transfers but the
method. WireGuard's IPv6 observables are the same three (`route6`,
`ip6_dst_lookup_flow`'s source selection, the sernum), served today by the
environment's two-case rule, and no campaign result in the three charters
depends on the IPv6 trie. The reason is cost against payoff, not a
profound exclusion: the design doc that opens the IPv6 lane says so.

## 8. Decisions and operands

In `fib_trie.c`, per function, the choice points in the C's order, each a
`Decision` with its spans; the ones whose operands the comparison stream
carries are `branchCmp` with both operands:

- `fib_table_lookup`: the empty trie (:1443); per step-1 node the index
  test (:1470, operands `index`, `1 << bits`), the leaf test (:1474), the
  `slen > pos` record (:1480); the null child (:1486); per step-2 node the
  prefix mismatch or `slen == pos` (:1499), the leaf (:1503); the backtrace
  loop's `cindex == 0` (:1522), the root (:1529); per alias the suffix
  test (:1561), DSCP (:1564), dead (:1567), scope (:1569), the error type
  (:1573), the dead flag (:1581), per nexthop `fib_lookup_good_nhc`'s three
  tests (:1411, :1414, :1419) and the `NOREF` flag (:1603).
- `fib_find_node`: the null child (:946), the index test (:965), the leaf
  loop (:971). `fib_find_alias`: the five comparisons (:997-1009).
- `fib_insert_node`: the taken slot (:1128); `fib_insert_alias`: the
  placement loop (:1172-1176) and the suffix update (:1188).
- `fib_table_insert`: the info error (:1219), the existing alias
  (:1238-1239), `NLM_F_EXCL` (:1243), the match loop (:1256-1262),
  `NLM_F_REPLACE` (:1269) with its match (:1275), its accessed flush
  (:1321), the match (:1330), `NLM_F_APPEND` (:1333), `NLM_F_CREATE`
  (:1339), the alias allocation (:1345), the insert error (:1361), the
  leaf (:1366), the notifier (:1371-1372), the default count (:1382).
- `fib_table_delete`: the leaf and alias (:1708, :1713), the match loop's
  six conditions (:1723-1736), the match (:1742), the default count
  (:1749), the accessed flag (:1754). `fib_remove_alias`: the emptied leaf
  (:1645), the suffix equality (:1646), the last node (:1655).
- `resize`: `should_inflate`'s three terms (:816), the inflate failure
  (:871), `max_work` (:886), `should_halve`'s three (:830), the halve
  failure (:894), `should_collapse` (:844 with the `KEYLENGTH` term at
  :840); `inflate`/`halve`/`collapse`'s per-child cases (:564, :568,
  :577, :598, :603, :659, :666, :695); `update_suffix`'s scan (:729, :738);
  `put_child`'s count updates (:427, :429, :436, :438, :441).
- `fib_table_flush`: the climb (:2021), the root (:2025), the suffix
  (:2029), the null and tnode children (:2044, :2047), per alias the
  keep conditions (:2055-2057, :2067).

The operands the stream already carries at these sites are in section 9's
table: the node positions, the bit counts, the keys and the thresholds,
distinct per trace, so a mutant of the arithmetic is rejected by the
operand check, not only by the outcome.

## 9. Measured on s4

Method: no guest boot was needed. `CONFIG_KCOV_INSTRUMENT_ALL=y`
instruments every file, so a check run's dump carries the routing code's
coverage although `net/ipv4` is not anchored: `coverage-map.json` and
`comparison-map.json` resolve the PCs to DWARF frames, `coverage.jsonl`
lists the PCs per trace and operation, `comparisons.jsonl` the compare
records with operands. `scripts/probes/c-fib-coverage.py <run dump>`
(committed with this note) reads them; the run read was the `wireguard`
suite on s4 of 2026-10-14 18:44 (261 traces, 28 chunk dumps, in the
index-lookup worktree's `.artifacts/check/20261014T184449Z`), and the
figures reproduce from any `wireguard` run dump on s4. `scripts/probes/c-fib-shape.py`
transcribes the C's insert and resize and prints the fixture's trie.

### 9.1 What the corpus reaches, inside the windows

| Function | Lines hit | Traces | Operations |
| --- | ---: | ---: | ---: |
| `fib_table_lookup` | 26 | 183 | 509 |
| `fib_lookup_good_nhc` | 4 | 175 | 494 |
| `prefix_mismatch` | 2 | 59 | 92 |
| `fib_table_delete` | 23 | 13 | 14 |
| `fib_table_flush` | 19 | 16 | 16 |
| `fib_remove_alias` | 11 | 13 | 13 |
| `resize` with `should_inflate`, `should_halve`, `should_collapse`, `collapse`, `update_suffix`, `put_child` | 6 + 3 + 3 + 1 + 7 + 6 + 8 | 19 | 19 |
| `fib_find_node`, `fib_find_alias` | 3, 9 | 17, 19 | 18, 23 |
| `fib_table_insert` | 17 | 4 | 4 |
| `inflate`, `halve`, `fib_insert_node`, `fib_insert_alias`, `leaf_new`, `tnode_new` | 0 | 0 | 0 |
| `ip_route_output_key_hash_rcu`, `__mkroute_output` | 19, 23 | 179, 175 | 497, 490 |
| `ip_route_input_slow` | 27 | 31 | 40 |
| `fib_validate_source` (the fast path only; `__fib_validate_source` 0) | 7 | 31 | 40 |
| `fib_create_info`, `fib_find_info`, `fib_nh_init` | 28, 11, 6 | 4 | 4 |
| `fib_sync_down_dev`, `fib_del_ifaddr`, `fib_magic`, `fib_add_ifaddr` | 18, 19, 6, 5 | 20, 10, 14, 4 | 21, 10, 14, 4 |
| `rt_cache_flush`, `rt_cache_valid`, `ipv4_dst_check` | 1, 2, 2 | 192, 152, 22 | 212, 338, 39 |

The lookup's shape is exercised: the backtrace loop (:1522) in 56 traces
(every transmit to a non-local destination descends to the `10/8` or
`127/8` branch and climbs to the `0/0` leaf), the step-2 prefix test
(:1499) in 59, the root's `-EAGAIN` (:1529) in 10 (`b1_down`, the
`l_delete_*` sends, `w9_unroutable`, `w9_deladdr_then_send`). The
`fib_table_insert` hits are the four `l_down_up_*` traces, where the
after-down `wg_up`'s `NETDEV_UP` re-adds the surviving address's local
route inside the ioctl and finds its alias present (the `fa_match` arm,
:1256-1262, then `-EEXIST`, which `fib_magic` ignores): no node is
inserted. The boot-time inserts of `lo` and the `route_into_wg0` requests
are outside every window: the guest captures the task's coverage count
at the syscall's return (`harness/guest.c:2534`) and issues the address
and route requests after the wait (`:2586-2601`). So an insertion of a
leaf or a tnode, an inflate or a halve has never been inside a window.
`fib_table_delete` is reached by the W9 `wg_delroute`/`wg_deladdr`
operations and `wg_delete`; `fib_table_flush` and the resize by `wg_down`,
`wg_delete`, `wg_set_mtu 0` and the W8 exits.

### 9.2 The decisions already in the stream

Compare records at the trie's sites, with distinct operand pairs (the
probe's second table):

| Site | Records | Distinct operand pairs | Operands seen |
| --- | ---: | ---: | --- |
| `fib_table_lookup:1470` (index vs `1 << bits`) | 2564 | 20 | `(1, 0x1fffe00)`, `(1, 0xafffe01)`, ... |
| `:1480` (`slen > pos`) | 1854 | 6 | `(0x16, 0x18)`, `(0x16, 0x16)`, ... |
| `:1499` (prefix mismatch, `slen == pos`) | 254 | 17 | keys `0x75000000`, `0xcafffc00`, `0xfe0100`, ... |
| `:1522`, `:1529` (backtrace, root) | 86, 11 | 2, 1 | `(0x1f, 0x20)` |
| `:1561`-`:1603` (the alias scan) | 689-705 each | 1-15 | the suffix masks |
| `resize:869`, `:892`, `:906`, `:907` | 166, 154, 93, 79 | 10, 7, 4, 6 | positions `0x16`, `0x1d`, bits 1 and 2 |
| `collapse:695`, `:700` | 54, 25 | 4, 2 | `(0x1f, 0x1d)`, `(0x1f, 0x20)` |
| `fib_table_flush:2025` (the climb) | 70 | 5 | `pn->pos` 0x16, 0x1a, 0x1d, 0x20 |
| `fib_table_delete:1707`-`:1754` | 71-13 | up to 10 | keys `0x100007f`, `0x1feff0a` |
| `fib_table_insert:1225`-`:1269` | 4-16 | up to 4 | |
| `ip_route_output_key_hash_rcu:2860` (the route's construction) | 11303 | 59 | |
| `ip_route_input_slow:2289`-`:2440` | 26-80 each | 1-3 | destinations `0x200000a`, `0x302010a`, `0x1feff0a` |

Every choice point of section 8 that the corpus reaches has its operands
in the stream already: the module's decisions are checkable on the
existing corpus from the first build, with no instrument added.

### 9.3 The fixture's tables and the trie's shape

From the C alone (1.8 and `route_into_wg0`), the namespace's one trie
holds, after `lo` up and a successful `wg_up`:

| Prefix | Type, scope, table | Origin |
| --- | --- | --- |
| `127.0.0.1/32` | local, host, LOCAL | `fib_add_ifaddr` :1140 for `127.0.0.1/8` |
| `127.0.0.0/8` | local, host, LOCAL | :1150-1153, loopback prefix route |
| `127.255.255.255/32` | broadcast, link, LOCAL | :1155-1157 |
| `10.255.254.1/32` | local, host, LOCAL | wg0's address, `/32`: no prefix or broadcast route |
| `0.0.0.0/0` | unicast, link, MAIN, oif wg0, no prefsrc | `route_into_wg0`'s `RTM_NEWROUTE` |
| `d/32` with `RTAX_MTU` per W4 route | unicast, link, MAIN | the routes mode |

Five leaves, and by the transcription (`c-fib-shape.py`) four tnodes:
the root's child at `pos 29, bits 2`, below it `pos 26, bits 2` holding the
`0/0` leaf and the wg0 host route, and `pos 22, bits 2` holding `pos 0,
bits 1` (the two `127.0.0.x` leaves) and the broadcast leaf; depth three.
Three inflates at setup (`pos 23 → 22`, `30 → 29`, `27 → 26`), no halve.
With a W4 host route a `pos 22, bits 2` node appears under the `10/8`
branch; depth stays three. The shape is cross-checked against the
kernel: the positions the stream records at the flush's climb
(`fib_table_flush:2025`: `pn->pos` 22, 26, 29) and at `collapse:700`
(`tp->pos` 29, 32) are exactly the transcription's nodes, and
`resize:869`'s `tn->pos` operands 22 and 29 are the nodes a deletion
resizes. The transcription is the build's starting point for the pure
core and its first unit test.

## 10. The corpus

A `routing` directory under `corpus/` with its own suite name, run with
the WireGuard groups at the claim point, and the generator's `routing`
class (`ROUTING_SHARE`, today 0.05) extended with route insertions:

- `wg_addroute family dst plen oif metric [mtu] [flags]`: `RTM_NEWROUTE`
  with `NLM_F_CREATE` and optionally `EXCL`, `REPLACE`, `APPEND`; the
  insert path with every arm of `fib_table_insert` (`-EEXIST`, replace,
  append, the new leaf, the new tnode) inside the window, and `resize`'s
  inflate; `wg_delroute` generalised to a destination and prefix so the
  delete's match arms and `halve` are reached;
- lookups at each depth: transmits to `127.0.0.1`, to `10.255.254.1`, to
  a `10.0.0.x` host route, to an address under `127/8` that is not a leaf
  (the step-2 fallback to the `/8`), to the default, with and without a
  source set;
- a longest-prefix tie: two aliases at one prefix with different metrics
  (the `fib_find_alias` priority order and `fib_select_default` when the
  prefix is `0/0`, `tb_num_default 2`), and one with a different DSCP;
- the default route's accessed flag: delete before and after a lookup
  (the existing `w9_delroute_untouched` and `w9_session_delroute_untouched`
  are the pair);
- an insertion sequence of eight `/32` routes under one `/24` and their
  deletion (inflate to four bits, halve back, collapse);
- `wg_addaddr` of a second wg0 address with a prefix shorter than 32 (the
  prefix and broadcast routes of `fib_add_ifaddr`) and its deletion (the
  `fib_del_ifaddr` scan);
- the input side: a decrypted packet to `127.255.255.255` (broadcast,
  `brd_input`), to the second address, to a `10.0.0.x` host route
  (`-EHOSTUNREACH`, no ICMP), replacing rows 10 and 13's exclusions by
  decisions.

About fourteen handwritten traces and the generator class. IPv6 traces
stay with the environment's rule.

## 11. One-off mutants

Run once, reported in the build's commit, then deleted, each on the
smallest subset:

1. the backtrace's bit strip (`cindex &= cindex - 1` → `cindex = 0`):
   rejected by any default-route transmit (56 traces today);
2. the `slen > pos` record dropped (:1480): rejected by the same;
3. `prefix_mismatch` without the `-prefix` term: rejected by a lookup
   under `127/8` that is not a leaf;
4. `should_inflate`'s root threshold 30 → 50: rejected by the insertion
   sequence's operands at `resize:869`;
5. the alias order in `fib_insert_alias` (`tb_id` ascending): rejected by
   the tie trace;
6. the accessed-flag condition at `fib_table_delete:1754` dropped:
   rejected by `w9_delroute_untouched` through the dst cache's generation
   (the rule the environment carries by hand today).

The sentinel set gains at most one entry (the lookup channel, item 1) if
the integration keeps it; the rest are deleted.

## 12. The proof tree

Files naming the routing environment (`routeLookup`, `route4`, `route6`,
`addrs4`, `defaultRoute4`, `ipv4Gen`, `routesPending`, `wgDelroute`,
`wgDeladdr`), read-only via `git show`:

- main (ca6b22e): 6 files: `Logged/Operations.lean`, `Logged/Syscalls.lean`,
  `WG/Keypairs/Evolution/Syscalls.lean`, `WG/Keypairs/Frames/{Env,Kernel,WGBase}.lean`;
- `proofs/campaign` (b1ec9e8): 20 files, the six above plus
  `Framing/{EnvOperations,Kernel,KernelEffects}.lean`,
  `WG/AllowedIps/RoutingSocketFrames.lean`, `WG/Cookies/Frames.lean`,
  `WG/Environment/BatchSource.lean`, `WG/Lifetimes/{EnvBatchAudit,EnvControlsAudit,EnvRemainingCalls,SocketSend,SocketSend4,SyscallDispatchAudit,SyscallsAudit}.lean`,
  `WG/Queues/RxRingSocket.lean`; `SocketSend4.lean` names them fifteen
  times;
- `proofs/campaign-2` (e56156e): the same six as main.

The change moves routing state from `World` to `Kernel` and replaces
`World.route4` by a lookup over it, so every frame over those `World`
fields and every `send4` frame repairs; the pure core is new and framed
once. Cost: hours on main and campaign 2, about two days on campaign 1
(the `SocketSend4` and `AllowedIps` frames), under lag-and-repair.

What campaign 3's routing composition needs from the module, stated as a
requirement on the build: the core (`tableLookup`, `tableInsert`,
`tableDelete`, `resize`) is pure and total over the inductive, with no
effect inside it (decisions and allocations reported by the wrapper), so
that the specification "the lookup returns the longest live prefix whose
alias passes the DSCP, scope and nexthop tests, in the C's order" is a
theorem about a function of the trie and the key; the trie's
well-formedness (keys consistent with `pos` and `bits`, counts exact,
aliases ordered) is a predicate the inserts and deletes preserve, stated
with the core; and `send4`'s route, the batch's inner route and the
receive predicate's local decision are each one call of the same
function on the namespace's trie, so the end-to-end relation from a
transmit's destination to the receiving socket composes through it. The
conventions note's items apply (properties over a projection, history on
the proof side).

## 13. Risks, estimate, decisions

Risks, the stopping one first:

1. The fixture's trie is constructed by the mirror from the C's rules
   with no insertion ever observed. If the construction differed, every
   declared lookup decision would mismatch from the first run. Mitigation
   already in hand: the transcription's node positions match the
   kernel's recorded operands (9.3), and the lookup's per-node operands
   (`:1470`, `:1480`, `:1499`) expose the walk at every lookup, so the
   first `wireguard` suite run on the built mirror settles it. If it does
   not settle, the remedy is an `RTM_GETROUTE` dump of the table at the
   trace's start to compare shapes, a harness change, not a kernel one.
2. The decision count: about fifteen declared decisions per lookup and
   up to twenty lookups per operation in the send-heavy traces; the
   checker's matching is linear and the operand rows grow by about a
   fifth of today's. Not a stop; measured at the first claim point.
3. Anchoring the three consumer files (U1) needs their cut lists exact;
   a function reached and not listed is a fail-closed red, found at the
   first run, cheap to fix.
4. The campaign-1 carry (two days) lands while R3's packet paths are
   open; the regime is merge-and-carry, not a prerequisite.
5. The decision at `__mkroute_output`'s cache hit (3.4) is observable
   only through an allocation that is a cut: a wrong cut would hide a
   `GFP_ATOMIC` failure arm. The arm is the environment's by the W4/W5
   boundary decisions; stated, not modelled.

Estimate, in three landings on s4 (the plan's "design 1 d, audit 0.5 d,
build 6 d" was the trie alone):

| Landing | Content | Days |
| --- | --- | ---: |
| C1 | `fib_trie.c` anchored; the trie's core, insert, delete, flush, resize; `fib_info` sharing; the fixture's tables constructed by the C's rules; `World.route4` and the generation bumps replaced; `send4`, the batch's `xmit` and `dst_mtu` on the trie; the `routing` corpus and generator class; mutants 1 to 6 | 4 |
| C2 | `fib_frontend.c` and `fib_semantics.c` anchored with their cut lists; the notifier arms, `wg_addaddr`; `fib_validate_source`'s fast path | 2 |
| C3 | `route.c`'s output and input sequences anchored; the receive rows 5 to 13 as decisions; the input corpus | 2 to 3 |
| settling, claim points | one per landing | 1 |

Nine to ten agent-days, about 1.0 WU at the plan's rate; C1 alone, which
unblocks campaign 3's composition, is four days plus its claim point.
Design: 0.5 day (this note).

Decisions for the user:

- U1: anchor `fib_frontend.c`, `fib_semantics.c` and `route.c` with cut
  lists (recommended, C2 and C3), or keep them mirrored but unanchored.
- U2: IPv6 deferred to its own lane (section 7).
- U3: the three-landing order, with C1 first for campaign 3, against one
  landing of the whole.
- U4: the module's home, `Leanux/Net/Fib/` and `Leanux/Net/Route.lean`, a
  new tree beside `FS`, `WG` and `Seccomp`.

Tactical, the fork's: the pure core with a thin wrapper; `fib_info` as a
map with reference counts; the parent pointer as an explicit path; the
corpus list of section 10; the mutant list of section 11.

[AGENT 2026-10-14] The measurement reads an existing run dump rather
than booting a guest: KCOV instruments every file on this configuration,
so the coverage and comparison streams of any `wireguard` run already
carry the routing code's decisions and operands.

[AGENT 2026-10-14] `resize` is in scope whole: reachable by the lane's
own corpus, its decisions recorded with operands, no profound reason
against.
