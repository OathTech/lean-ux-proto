# Design C: the IPv4 FIB trie as a mirror module — 2026-10-14, revised 2026-10-15 [AGENT, fork of the coordinator]

Lane C of [the parallel plan](2026-10-14-wireguard-parallel-plan.md):
`net/ipv4/fib_trie.c` as a new mirror module with its own corpus, record-only
hooks if any, frames only for the proofs. It is the plan's critical path:
campaign 3's end-to-end routing composition needs the output route and the
input route to be mirrored code with a contract boundary, not the
environment's summary. Read-only against Linux 6.12.110 (`.deps/linux`) and
the s4 oracle (identity `6b2018b9`); the mirror at main ca6b22e. No
implementation. Sections 2 and 9 are measured; everything else is the C
verified by line. Revision 2 answers
[the independent review](2026-10-15-design-c-review.md) (1cfadd5, produced
by a Claude Opus 5.5 reviewer; the dispositions are section 14).

Summary. The fixture's routing is one small LC-trie: four internal nodes
and five leaves after boot (section 9), shared by the local and main
tables on this configuration. Its lookups run inside the coverage window
in 183 of 261 WireGuard traces from four callers (the output route, the
input route, the neighbour constructor's address classification, the
address deletion's classification), with the backtrace in 56 and the
no-route miss in 10, and every decision of the lookup, the delete, the
flush and the resize already lands in the comparison stream with its
operands. The trie itself needs no kernel change; the route paths around
it carry three hidden inputs the environment must treat (section 5).
What the window never contains is an insertion of a node: the boot-time
and `route_into_wg0` inserts run before or after the per-operation
capture, so the mirror constructs the trie from the C's rules, a
`/proc/net/fib_trie` read outside the window checks the shape exactly,
and the corpus adds route insertions inside the window. The module
replaces the environment's six hand-written generation bumps and its
two-case route function with the C's own `rt_cache_flush` sites and
`fib_table_lookup`. IPv6 is deferred to its own lane (section 7).
Estimate: fifteen to eighteen agent-days in three landings (section 13);
the first, the trie with both lookups, is what campaign 3 waits for, at
about ten days from the design.

## 1. The C, verified

Configuration (`kernel/config-x86_64-net-choice`): `CONFIG_IP_ADVANCED_ROUTER`
unset, hence `CONFIG_IP_MULTIPLE_TABLES` unset; `CONFIG_IP_FIB_TRIE_STATS`
unset; `CONFIG_IP_ROUTE_MULTIPATH` unset; `CONFIG_IPV6=y` with
`CONFIG_IPV6_MULTIPLE_TABLES` unset; `CONFIG_PROC_FS=y`.

### 1.1 One trie for two tables

Without `IP_MULTIPLE_TABLES`, `fib4_rules_init` (fib_frontend.c:50-71)
creates the main table and then the local table as an *alias* of it:
`fib_trie_table(RT_TABLE_LOCAL, main_table)` (fib_trie.c:2390-2420) shares
`tb_data`, so both tables are one `struct trie` whose aliases are told
apart by `fa->tb_id`. `fib_get_table`/`fib_new_table` are the inline
versions in `include/net/ip_fib.h` (the `#ifndef CONFIG_IP_MULTIPLE_TABLES`
block): `fib_lookup` (ip_fib.h:314-328) looks the main table up once and
maps `-EAGAIN` to `-ENETUNREACH`. Because the two table entries share
the trie, `fib_flush` (fib_frontend.c:184-197), which walks the table hash,
runs `fib_table_flush` twice over the one trie, MAIN (index 254) then
LOCAL (255): the first pass removes the dead aliases and resizes on the
way up, the second finds nothing.

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
(:320-336, the calls at :333 and :335). `leaf_new` is
`kmem_cache_alloc(trie_leaf_kmem, GFP_KERNEL)` (:354-375), `tnode_new` sets
the key to its significant bits and `slen = pos` (:377-401). `put_child`
maintains the empty and full counts and raises the parent's `slen`
(:418-444); `tnode_full` is "an internal child with no skipped bits"
(:407-413). `update_children` (:447-468) walks a new node's children and
either recurses into a child whose parent is already the new node (a node
created in the same step) or re-parents it (:462-465): the test at :462
is on parent identity. Frees are `call_rcu` (:309-317) and `tnode_free`
calls `synchronize_net` once `tnode_free_size` passes
`sysctl_fib_sync_mem` (:490-506): neither has an observable.

### 1.4 Resize (fib_trie.c:508-911)

`replace` (:508-533) links a new node in the old one's place, runs
`update_children`, frees the old node and then resizes every full child
of the new node (:526-531). `inflate` doubles a node's child array
(`pos - 1`, `bits + 1`), splitting full children into two half nodes and
lifting the others (:537-630); `halve` does the reverse (:633-686);
`collapse` removes a node with one child or none (:688-707);
`update_suffix` recomputes `slen` by a strided scan (:709-743).
`should_inflate` is `used > 1 && tn->pos && 50 * used >= threshold` with
`used = child_length - empty + full` and the root's threshold (:804-817);
`should_halve` is `used > 1 && bits > 1 && 100 * used < threshold`
(:819-831); `should_collapse` is `used < 2` (:833-845, the `KEYLENGTH` term
at :840-841). `resize` inflates while it should (at most `MAX_WORK` 10
steps), returns if it inflated at all, else halves while it should, then
collapses (:847-911); on an allocation failure a step is skipped and the
loop breaks (:871-877, :894-900). `trie_rebalance` resizes up to the root
(:1104-1108).

### 1.5 Find, insert, delete, flush

`fib_find_node` descends by `get_cindex` until a leaf (:971) or a null
child (:946) or a mismatch (`index >= 1 << bits`, :965) and returns the
parent (:936-973). A leaf's alias list is ordered by `slen` **ascending**
(the longest prefix first) and, at equal `slen`, by `tb_id` descending,
and within that by priority ascending: `fib_find_alias` skips aliases
with a smaller `slen`, stops at the first larger one and at a smaller
`tb_id`, and returns the first alias at `(slen, tb_id)` whose DSCP and
priority fit (:983-1013); `fib_insert_alias` places a new alias before the
first with a larger `slen` or, at equal `slen`, a smaller `tb_id`
(:1172-1177), or before the alias `fib_find_alias` returned (:1167-1168).
`fib_insert_node` allocates the leaf, and if the slot is taken (:1128)
creates a one-bit tnode at `__fls(key ^ n->key)` holding both, pushes the
suffix and rebalances (:1110-1158); the suffix update is at :1188.
`fib_table_insert` (:1200-1398): `fib_create_info` first (shared infos,
1.7); an existing alias with the same DSCP and priority is `-EEXIST` under
`NLM_F_EXCL` (:1243), replaced under `NLM_F_REPLACE` (:1269-1324, the new
alias allocated at :1281, with `rt_cache_flush` only if the old alias was
accessed, :1321-1322), or appended (:1330-1335); `NLM_F_CREATE` is required
for a new one (:1339), allocated at :1344 and inserted at :1360; a prefix
of length 0 counts `tb_num_default` (:1382-1383); then `rt_cache_flush`
unconditionally (:1385). `fib_table_delete` (:1694-1759) finds the leaf and
the alias (`-ESRCH` at :1708-1709 and :1713-1714), matches type, scope,
prefsrc, protocol, nexthop and metrics (:1721-1743), notifies, decrements
`tb_num_default` for a default (:1749-1750), removes the alias
(`fib_remove_alias`, :1632-1661: frees an emptied leaf (:1645) and
rebalances, else, when the removed alias was the last of the list,
takes the leaf's `slen` from the new last alias and pulls the suffix,
:1655-1660), flushes the cache only if `FA_S_ACCESSED` (:1754-1755), and
releases the info. `fib_table_flush` (:2006-2096) walks the trie in
reverse, deletes the aliases whose info is `RTNH_F_DEAD` (or everything
with `flush_all`), updating suffixes and resizing each node on the way
up.

### 1.6 Lookup (fib_trie.c:1401-1630)

`prefix_mismatch` is `(key ^ prefix) & (prefix | -prefix)` (:1401-1406): it
tests the bits from the prefix's lowest set bit upward.
`fib_table_lookup` with `key = ntohl(daddr)`: an empty trie returns
`-EAGAIN` (:1442-1446). Step 1 descends by `get_cindex`, breaking on a
skip-bit mismatch (:1470) or a leaf (:1474), recording `pn`/`cindex` only
at nodes with `slen > pos` (:1480-1483), and goes to backtrace on a null
child (:1486-1487). Step 2 backtracks: at a node whose prefix mismatches or
whose `slen == pos` it strips the lowest set bit of `cindex`
(:1499, :1543) and climbs when `cindex` is 0 (:1522-1540), returning
`-EAGAIN` at the root (:1529-1532). Step 3 scans the leaf's aliases: an
alias is skipped if the key differs from the leaf's key above the
alias's suffix, in its prefix bits (:1561-1562), on a DSCP mismatch
(:1564), a dead info (:1567), a scope narrower than the flow's (:1569);
then `fib_alias_accessed` sets `FA_S_ACCESSED` (:1571), a write to the
alias, an error type returns its error (:1573-1579), a dead-flagged info
is skipped (:1581), and the first nexthop that passes `fib_lookup_good_nhc`
(dead, linkdown, `oif`; :1409-1423) fills the result after the `NOREF`
test (:1603): prefix, prefix length, nexthop, type, scope, DSCP, info,
table, alias head (:1606-1616). A leaf with no usable alias falls back to
the backtrace (:1621-1629).

### 1.7 fib_info (fib_semantics.c)

`fib_create_info` (:1415-1660) validates type, scope and flags, allocates
the info (`kzalloc`, :1489; the info hash may grow by `kvzalloc` when the
global count reaches the global size, :1468-1486), copies protocol, scope,
flags, priority, prefsrc, type and table, initialises the one nexthop
(`fib_nh_init`, :652, whose `fib_nh_common_init` allocates the per-cpu
output cache, :621-623), and for `RT_SCOPE_HOST` takes the device by `oif`
with `fib_nh_scope = RT_SCOPE_NOWHERE` (:1562-1584), else runs
`fib_check_nh` (:1585-1597), which without a gateway is `fib_check_nh_nongw`
(:1244-1275, the tests at :1250, :1260, :1263 and :1271: `-ENODEV` without an `in_device`, `-ENETDOWN` when the device
is down, scope HOST, `RTNH_F_LINKDOWN` when the carrier is off);
`fib_valid_prefsrc` (:1391-1412: a local route whose destination is its
prefsrc passes at once, any other prefsrc is classified by
`inet_addr_type_table`, a trie lookup); `fib_info_update_nhc_saddr` picks
the nexthop's source by `inet_select_addr` and caches it with the
namespace's `dev_addr_genid` (:1354-1369); then `fib_find_info` returns an
identical existing info with `fib_treeref` incremented (:1615-1621; the
comparison at :409-437 is protocol, scope, prefsrc, priority, type, table,
metrics, flags and nexthop), else the new one is hashed and linked to its
device bucket (:1622-1649). `fib_release_info` unhashes at the last tree
reference and marks `fib_dead` (:261-285). `fib_sync_down_dev` walks the
device's bucket of the global nexthop hash, skipping nexthops of other
devices and infos already seen (:2015-2021), marks every nexthop on the
device dead or linkdown and counts the infos that went fully dead
(:2004-2068); `fib_flush` then removes their aliases. `fib_select_path` with
a single path only chooses a source when the flow has none
(`fib_result_prefsrc`, :1372-1388: the info's prefsrc, else the cached
nexthop source while its generation matches `dev_addr_genid`, else a fresh
`inet_select_addr`; :2269-2298), and `fib_select_default` runs only with
`tb_num_default > 1` (:2283-2285): it scans the default aliases (:2070-2150),
skipping each candidate whose nexthop has no gateway of link scope
(:2104-2106), so on this fixture, whose routes have no gateway, it
assigns nothing. `fib_props` (:99-147) maps types to errors and minimum
scopes.

### 1.8 What a device's address adds (fib_frontend.c:1083-1343)

`fib_magic` builds a `RTPROT_KERNEL` config with the address as prefsrc
and the device as `oif`, `NLM_F_CREATE | NLM_F_APPEND`, table LOCAL for
local and broadcast types and MAIN for unicast, scope HOST for local
types else LINK, and inserts or deletes (:1083-1121). `fib_add_ifaddr`
adds the `/32` local route of the address (:1140), and if the device is up
(:1142) the explicit broadcast (:1146-1150), the prefix route for a prefix
shorter than 32 (local on a loopback device, unicast otherwise;
:1152-1159) and the network broadcast for a prefix shorter than 31
(:1161-1164). `fib_del_ifaddr` removes them, keeping those another address
still justifies (:1197-1343); after removing the `/32` it classifies the
address with `inet_addr_type_dev_table`, a trie lookup, and if the address
is gone and no longer local it runs `fib_sync_down_addr` over the global
prefsrc hash and `fib_flush` (:1328-1344). The notifiers: `NETDEV_UP` of an
address or a device adds, `NETDEV_DOWN` of the last address disables IP
on the device (`fib_disable_ip`: `fib_sync_down_dev`, `fib_flush` and
`arp_ifdown`, :1436-1444, :1461-1469), a device's `NETDEV_DOWN` disables
without force, and `NETDEV_CHANGEMTU` runs `fib_sync_mtu` and
`rt_cache_flush` (:1477-1530); each address event and the device's `UP`
also bump `dev_addr_genid` (:1458, :1463, :1505). The loopback gets
`127.0.0.1/8` at its `NETDEV_UP` (devinet.c:1601-1613). A `RTN_LOCAL`
route added over rtnetlink sets `fib_has_custom_local_routes`
(:918-919), which moves `fib_validate_source` to its full path (1.9).

### 1.9 From the trie to a route (route.c), and the other callers

Output: `ip_route_output_key_hash_rcu` (:2696-2864) rejects a multicast,
limited-broadcast or zeronet source with `-EINVAL` (:2706-2712), a source
that is not a local address with `-ENETUNREACH` (:2714, :2751-2754; the
test is `__ip_dev_find`, devinet.c:153-180, which falls back to a lookup
of the local table when the source is not an interface address), takes
the loopback for an empty destination (:2788-2795), calls `fib_lookup`
(:2799), returns its error unless an `oif` was given (:2800-2830), takes
the local route with the prefsrc or the destination as source
(:2833-2841), else `fib_select_path` and the result's device (:2855-2857),
and builds the route in `__mkroute_output` (:2545-2665): the per-nexthop
cached route is reused when `rt_cache_valid` (:2633-2634), else
`rt_dst_alloc` (`dst_alloc`, a `GFP_ATOMIC` allocation, :1668-1693) and
`rt_set_nexthop` with the info's metrics (:1609-1660).

Input, in the C's order. `ip_rcv_finish_core` (ip_input.c:321-421) runs the
early demux for UDP when the packet has no dst yet (:334-352); on this
fixture `udp_v4_early_demux` (udp.c:2626-2660) finds no connected socket
and sets nothing, so the route is looked up. A packet delivered over the
loopback carries its output dst (`loopback_xmit` keeps it), so only wg0's
decrypted packets reach `ip_route_input_noref`. `ip_route_input_rcu`
(:2479-2527) takes the multicast branch first; `ip_route_input_slow`
(:2265-2477) returns `-EINVAL` without an `in_device` (:2282-2284, the
device below 68 bytes of MTU), drops a multicast or limited-broadcast
source (:2296), goes to `brd_input` for the limited-broadcast destination
or an all-zero pair (:2301-2302), drops a zeronet source (:2307), a zeronet
destination (:2310), a loopback destination (:2316-2318, `route_localnet`
0) and a loopback source (:2319-2321), calls `fib_lookup` (:2347), maps a
miss to `-EHOSTUNREACH` with forwarding off (:2348-2352), goes to
`brd_input` for `RTN_BROADCAST` (:2354-2360), delivers a `RTN_LOCAL` result
after `fib_validate_source` (:2363-2368), refuses to forward (:2371-2373),
treats any other type as a martian destination (:2375-2376), and builds
the input route (:2396-2443). `fib_validate_source`'s fast path on this
configuration (`rp_filter 0`, `accept_local 0`, no custom local routes)
is `inet_lookup_ifaddr_rcu(src)`: a local source is `-EINVAL`, anything
else passes with no trie lookup (fib_frontend.c:421-451); with a custom
local route it is `__fib_validate_source`, two trie lookups (:344-419).

The other callers of `fib_table_lookup` the fixture reaches:
`__inet_dev_addr_type` (fib_frontend.c:206-234) classifies an address by a
lookup of the local table (:225-229) after the zeronet, limited-broadcast
and multicast early returns (:215-218); its callers inside the window are
`arp_constructor` (arp.c:242, `neigh->type` at a neighbour's creation;
NOARP devices get `NUD_NOARP` entries, :249-252), `fib_del_ifaddr`
(fib_frontend.c:1334), `__inet_bind` (af_inet.c:493, with `INADDR_ANY`,
an early return) and the multicast joins (`ip_mc_up`, igmp.c:1484-1486,
an early return), and from the corpus's insertions `fib_valid_prefsrc`.
`fib_compute_spec_dst` (fib_frontend.c:271-310) runs `fib_lookup` only for
a non-local route's source, not for the local deliveries the fixture
receives. The neighbour entries `arp_constructor` creates are never
collected on this fixture: `neigh_periodic_work` returns before its scan
while the table holds fewer than `gc_thresh1` (128) entries
(neighbour.c:980), and `arp_ifdown` removes a device's entries at its down
and unregister (fib_frontend.c:1443). `rt_cache_flush` is
`rt_genid_bump_ipv4` (route.c:406-409); `rt_cache_valid` and
`ipv4_dst_check` compare a route's generation with the namespace's
(:1602-1607, :1245-1248). The flush is also called by
`ip_rt_multicast_event` at every multicast join (:3445-3448, from
igmp.c:1484-1486), by `nh_netdev_event` on `NETDEV_CHANGEMTU`
(nexthop.c:3884-3887, a second flush beside fib_frontend.c:1521-1522), by
`arp_netdev_event` on `NETDEV_CHANGEADDR` (arp.c:1330-1332) and by the
devinet sysctls (devinet.c:2421-2509), none of which the fixture changes.

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
(`Env/IpStack.lean:172-174`). Neighbour entries are not represented.

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
  Nat) (fresh : Bool)`, with the root as the C's `pos = 32` node holding
  one child. The parent pointer is not represented: the walks keep their
  path as an explicit stack, which is what `resize`, `node_pull_suffix`
  and the backtrace read from it; `update_children`'s test on parent
  identity (:462) is reproduced by the `fresh` mark, set on the nodes a
  resize step creates and cleared when the step ends, so the decision is
  declared without operands (its operands are kernel pointers). The
  counts are kept as data, not recomputed, because
  `should_inflate`/`should_halve` compare them and the comparison's
  operands are checked. The nested inductive (an array of optional
  subtrees) is the C's shape; its cost in Lean is named in section 12.
- `FibAlias`: `slen`, `tbId`, `dscp`, `type`, `accessed` (the
  `FA_S_ACCESSED` bit), `info : FibInfoId`, `faDefault`.
- `FibInfo`: `protocol`, `scope`, `flags` (`RTNH_F_DEAD`/`LINKDOWN`),
  `priority`, `prefsrc`, `type`, `tbId`, `metrics` (the `RTAX_MTU` the W4
  routes carry), `dead`, `treeref`, and one nexthop: `oif`, `dev`,
  `nhScope`, `nhFlags`, `nhSaddr`, `nhSaddrGenid`, `gwFamily` (always
  none here). Kept in `Kernel.fibInfos : TreeMap FibInfoId FibInfo` with
  the sharing of `fib_find_info` as the C's identity rule: the fixture
  shares the `127.0.0.1/32` and `127.0.0.0/8` local routes' info (same
  protocol, scope, prefsrc, priority, type, table, metrics and nexthop),
  so a `fib_release_info` of one leaves the other's reference.
- `FibTable`: `tbId`, `numDefault`, and the trie; the local table an
  alias of the main as in 1.1: one `Kernel.fib4 : FibTrie` per namespace
  (the W8 foreign-creator mode has two namespaces; B2 adds a third device
  state: the table lives beside the namespace's other per-net state),
  with the namespace's `devAddrGenid` and `rtGenid` beside it.
- `Neighbours`: the per-device set of neighbour entries `(ifindex,
  address, type)` the C creates on first use and removes at `arp_ifdown`
  (1.9), in the environment (`World`), since the neighbour table is the
  stack's; the classification lookup at creation is the module's.

The address lists stay the environment's (`World.addrs4`), since
`in_device`, `inet_select_addr` and `inet_lookup_ifaddr_rcu` are
devinet.c, outside the lane; the module consumes them where the C does.

### 3.2 Functions, the C's control flow

`Leanux/Net/Fib/Trie.lean`, each with its decisions declared in
`fib_trie.c` (section 8):

- the core: `findNode`, `findAlias`, `insertNode`, `insertAlias`,
  `removeAlias`, `resize` with `inflate`, `halve`, `collapse`, `replace`,
  `updateChildren`, `updateSuffix`, `pushSuffix`, `pullSuffix`,
  `trieRebalance`, and `tableLookup` with its three steps, as total
  functions over `KeyVector`. `tableLookup : Trie → Flow → Result ×
  Option AliasPosition` returns the result and the position of the
  alias whose `FA_S_ACCESSED` bit the C sets (:1571), and the monadic
  wrapper applies that write; the core has no effect of its own, so the
  lookup's specification is a statement about a function. The wrapper
  reports each C choice point in order with its operands (`branchCmp` for
  `index >= 1 << bits`, the thresholds, `slen` comparisons) and consumes
  the allocation outcomes;
- `tableInsert`, `tableDelete`, `tableFlush` as the C's sequences over
  `fib_create_info`, `fib_find_info`, `fib_release_info`,
  `fib_sync_down_dev`, `fib_sync_down_addr`, `fib_check_nh_nongw`,
  `fib_valid_prefsrc`, `fib_result_prefsrc`, `fib_select_path`
  (`Leanux/Net/Fib/Semantics.lean`), with the `rt_cache_flush` calls at the
  C's sites: these replace the six generation bumps of the environment,
  and `defaultRoute4Accessed` by the alias's own bit;
- the entry points the fixture reaches (`Leanux/Net/Fib/Frontend.lean`):
  `fibMagic`, `fibAddIfaddr`, `fibDelIfaddr`, `fibDisableIp`, `fibFlush`
  (two passes, 1.1), `inetDevAddrType`, the `fib_inetaddr_event` and
  `fib_netdev_event` arms for `NETDEV_UP`, `NETDEV_DOWN`,
  `NETDEV_UNREGISTER` and `NETDEV_CHANGEMTU` with the `dev_addr_genid`
  bumps, `fibValidateSource`'s fast path, `rtmToFibConfig` and
  `inetRtmDelroute`/`inetRtmNewroute` for the corpus's route operations;
- the consumers of the lookup in C1, every in-window caller the dump
  shows (section 9.1): the output route (`Leanux/Net/Route.lean`,
  `ipRouteOutputKeyHash`'s decision sequence down to `{dev, src, type,
  mtu}` for `send4`, the batch's `xmit` and `wg_xmit`'s `dst_mtu`); the
  input route (`ipRouteInputSlow`'s sequence from the martian tests
  through `fib_lookup` to the `RTN_LOCAL` delivery, the `-EHOSTUNREACH`
  drop and the martian destination, consumed by the receive predicate in
  place of rows 5 to 13); the neighbour constructor's classification at
  the first transmit to a next hop on a device (`inetDevAddrType` from the
  environment's transmit, with `World.neighbours`); `fib_del_ifaddr`'s
  classification; `fib_valid_prefsrc`'s for the corpus's prefix routes.
  `__ip_dev_find`'s fallback is unreachable on this fixture (a source
  that is not an interface address never reaches `send4`, whose sources
  are learned from received datagrams' local destinations, nor the
  batch, whose sender binds the wildcard) and stays `unsupported`;
  `fib_compute_spec_dst`'s lookup likewise (the fixture receives only
  local deliveries); `__fib_validate_source` is refused with the custom
  local route that would enable it (the validator rejects a
  `wg_addroute` of type local), fail-noisy.

Environment rules that move into the mirror: `World.route4`, the six
generation bumps, `routeIntoWg0`'s and `wgDown`/`wgDelete`/`wgDeladdr`/
`wgDelroute`'s table edits (they become the C's notifier and rtnetlink
sequences on the trie), the receive rows 5 to 13 for IPv4. Rules that
stay: `routesPending` and its timing (the fixture's order, 14.3b of the
W9 design); the address lists; the W4 `routes` list as the source of the
fixture's `RTM_NEWROUTE` requests (now inserted into the trie with their
`RTAX_MTU`, so `dst_mtu` reads the alias's info instead of the list); the
dst cache; the neighbour set; `World.route6` and everything IPv6
(section 7); the per-nexthop route cache and `rt_dst_alloc` (3.4).

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
| the neighbour's type at its creation | `arp_constructor` → `inet_addr_type_dev_table` | the environment's transmit, first use of a next hop |
| the decrypted packet's input route: local, unreachable, martian | `ip_route_input_slow` → `fib_lookup`, `fib_validate_source` | the receive predicate rows 5 to 13 |
| the route generation the dst cache checks | `rt_cache_flush` at the insert, delete, notifier, multicast-join and flush sites | `dstCacheGet`'s generation test |
| `-ENETUNREACH` with no default route; `-ESRCH`, `-EADDRNOTAVAIL`, `-EEXIST`, `-ENETDOWN` of the route operations | `fib_lookup`'s `-EAGAIN` mapping; `fib_table_delete`, `fib_table_insert`, `fib_check_nh_nongw` | the W9 and corpus operations' results |

Not depended on and not modelled: the route's `rt_iif`, `rt_uses_gateway`,
the uncached list, the input route cache, the per-cpu output cache.

## 5. Hidden inputs, records and allocation sites

The trie has no hidden input of its own: `fib_table_lookup`,
`fib_table_insert`, `fib_table_delete`, `fib_table_flush`, `resize` and
their helpers read only the trie, the flow and the config, and
`fib_info_hashfn` has no seed. The route paths around it have three, and
the lane treats each:

- (a) `dev_addr_genid`: a per-namespace counter seeded with
  `get_random_u32()` at the namespace's creation (route.c:3660-3666),
  bumped at the address and device events (fib_frontend.c:1458, :1463,
  :1505), cached per nexthop (`nh_saddr_genid`, fib_semantics.c:1367) and
  compared at every source selection through a nexthop without prefsrc
  (:1383-1384). The dump shows the comparison in 73 records with 43
  distinct random operand pairs in 43 traces. The outcome is the equality
  of two relative values, so the mirror carries `devAddrGenid` and the
  per-nexthop cache as counters from 0 and the comparison is declared
  with an `operand_exclusions` entry (`correspondence/kcov.json`) for its
  two operands; no kernel change. A record-only hook at :3665 would make
  the operands exact only for namespaces created inside a window (the
  W8 mode's), not for the fixture's, whose creation precedes the capture;
  it is not proposed.
- (b) `net->hash_mix`: `get_random_bytes` at the namespace's creation
  (net_namespace.c:330), outside every window. It chooses the bucket of
  the global nexthop hash (`fib_info_devhash_bucket`,
  fib_semantics.c:330-335) and of the global prefsrc hash that
  `fib_sync_down_dev` (:2015-2021) and `fib_sync_down_addr` walk; those
  hashes are shared by every namespace on the box, so the walk's skip of
  a foreign nexthop (:2021, uncovered in the dump) depends on a random
  collision with another device's or namespace's bucket, including a
  previous trace's namespace before its `cleanup_net`. No record at the
  draw makes that exact. Treatment: the mirror walks only the
  namespace's nexthops on the device, and the skip at :2021 (and the
  corresponding test in `fib_sync_down_addr`) is a declared cut in the
  decision table with the note "global hash state", excluded from the
  unreported-decision check at that line, with a one-off mutant that
  reports a wrong outcome elsewhere in the walk. Decided before C2,
  where `fib_semantics.c` is anchored (U1).
- (c) the global info count against the global hash size
  (fib_semantics.c:1468; `(0x10, 0x3)` in the four in-window cases): the
  count includes other namespaces' infos. Treatment: the decision is
  declared, its operands excluded, and the environment's rule is that
  the hash does not grow during a trace; a `true` outcome is a red the
  check reports, never absorbed.

Allocation outcomes, all `GFP_KERNEL` in task context (class b-task,
[the allocation design](2026-10-05-a-alloc.md)), each an `AllocSite`
entry (`.exact 1`), harness-side: the kind-305 hook is generic in
`slab_alloc_node` and records a site when its address is in the armed set
the guest loads (`gen-choice-stream.py:1466-1495`, `harness/steer.py:342-362`):
`leaf_new` (fib_trie.c:359), `tnode_alloc`'s `kzalloc` (:333; the `vzalloc`
arm at :335 is not a slab call and needs more than 511 children, out of
reach), the alias allocations (:1281, :1344), `fib_create_info`'s `kzalloc`
(fib_semantics.c:1489) and the hash growth's two `kvzalloc` (:1477-1478,
unreachable by (c)), `ip_fib_metrics_init`'s `kzalloc` (metrics.c:74-76,
every route with a metric). `fib_nh_common_init`'s `alloc_percpu_gfp`
(fib_semantics.c:621-623) is a per-cpu allocation, lax and unsteerable as
`dstCacheInit` was retired (a-alloc.md, section 10): a constant-outcome
decision, not a site. Note that the four in-window `fib_table_insert`
traces already allocate an info and its per-cpu array and free them
when `fib_find_info` finds the shared one (fib_trie.c:1218 runs before
the `-EEXIST` test at :1243); unarmed today, these sites record nothing.
Failure arms are modelled as the C's (`-ENOMEM`, `-ENOBUFS`, the `resize`
step skipped) and reachable only when armed; the armed set is per trace
and the 64-range limit is not approached (seven sites).

Oracle changes: none for the trie, and none for the three hidden inputs
as treated above (two operand exclusions and one decision cut, each an
instrument on the trust surface with its one-off mutant). The lane
lands on s4.

## 6. Anchoring

`net/ipv4/fib_trie.c` is anchored in `correspondence/kcov.json` from C1
with every reached function listed (the 26 of section 9, of which
`fib_free_table` and `fib_proc_exit` are the namespace exit's, cut with a
note as the W8 teardown is) and the dump and proc functions listed as
unreached inside the window. Once it is anchored, every in-window call of
a trie function needs a mirror counterpart, whatever file the caller is
in (the checker's "Linux ran a decision function the mirror reported
nothing in", `evaluator/check.py:1166-1176`): that is why the callers of
3.2 are C1 consumers, mirrored unanchored until their files are anchored,
and why none of them can be a cut.

For `fib_frontend.c`, `fib_semantics.c` and `route.c` (U1): anchoring them
lists the reached functions the module mirrors and cuts the rest by name
(`__inet_bind`'s and the multicast joins' early-return classifications,
`fib_compute_spec_dst`, the notification builders, the proc and sysctl
exits, `__ip_select_ident` and `ip_idents_reserve`, already the cut sites
20 and 21). Two obstacles the review found:

- `fib_semantics.c` holds helpers IPv6 calls inside the window:
  `fib_nh_common_init` (185 traces, from `fib6_nh_init`, net/ipv6/route.c,
  at every `wg_up`), `fib_nexthop_info` (189 traces, from `rt6_fill_node`)
  and `fib_nh_common_release`. The function lists are per function, not
  per caller, so one of these cannot be mirrored for IPv4 and cut for
  IPv6. Options: a per-caller cut keyed on the outermost frame (an
  instrument change with its one-off mutant), or keeping
  `fib_semantics.c` unanchored with its IPv4 decisions mirrored and
  undeclared. The note recommends the per-caller cut, built in C2 before
  the file is anchored, since undeclared decisions are the thing the
  lane exists to remove.
- `route.c` sits under the boundary decision of [USER 2026-10-07]
  ("stop at the boundary of wireguard"; `docs/decisions.md:79-87`), which
  the census records as "reached only where WireGuard's observables
  depend on it"; anchoring it revises that decision, and the input
  corpus's `-EHOSTUNREACH` path reverses the [AGENT 2026-10-08] deferral
  of `ip_error` (`decisions.md:107-111`). U1 says so and is the user's.

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
Consequently campaign 3's end-to-end routing composition is an IPv4
result, which its charter must say (section 12).

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
  :840); the `&& max_work` terms of the two loops (:869, :892) are
  declared and unwitnessed (ten successive inflates need about a
  thousand children); `inflate`/`halve`/`collapse`'s per-child cases
  (:564, :568, :577, :598, :603, :659, :666, :695); `replace`'s full-child
  test (:530); `update_children`'s null child (:455) and parent identity
  (:462, without operands, 3.1); `update_suffix`'s scan (:729, :738);
  `put_child`'s count updates (:427, :429, :436, :438, :441).
- `fib_table_flush`: the climb (:2021), the root (:2025), the suffix
  (:2029), the null and tnode children (:2041, :2044), per alias the
  keep conditions (:2055-2057, :2067).
- in `fib_semantics.c` (C2): `fib_select_default`'s scan (:2082-2106, each
  candidate skipped at :2104-2106 on this fixture), `fib_result_prefsrc`'s
  three tests (:1376, :1379, :1383 with the operand exclusion of 5(a)),
  `fib_check_nh_nongw`'s four (:1250, :1260, :1263, :1271),
  `fib_valid_prefsrc`'s (:1393-1405), the walk of `fib_sync_down_dev`
  with :2021 cut (5(b)), the hash growth (:1468, operands excluded, 5(c)).

The checker's semantics for these decisions (`evaluator/check.py:1019-1030`,
`:1095-1110`, `:1138-1142`, `:1230-1245`): a trie decision repeats within an
operation, so it is declared `repeatable`; for a repeatable decision the
check compares the set of outcomes per operation, waives the
opposite-outcome test when both outcomes are reported, and requires each
operand pair the mirror reports to exist among the kernel's rows at that
site in the operation, surplus kernel rows allowed. So the existing
corpus checks the walk's outcome sets and operand sets per operation,
not its steps: a mirror that took fewer steps and reported a subset of
the kernel's pairs would pass on those traces. The exact checks of the
shape and of the walk are section 9.4's oracle and section 10's
destinations.

## 9. Measured on s4

Method: no guest boot was needed. `CONFIG_KCOV_INSTRUMENT_ALL=y`
instruments every file, so a check run's dump carries the routing code's
coverage although `net/ipv4` is not anchored: `coverage-map.json` and
`comparison-map.json` resolve the PCs to DWARF frames, `coverage.jsonl`
lists the PCs per trace and operation, `comparisons.jsonl` the compare
records with operands. `scripts/probes/c-fib-coverage.py <run dump>`
(committed with this note) reads them; the run read was the `wireguard`
suite on s4 of 2026-10-14 18:44 (261 traces, 28 chunk dumps, in the
index-lookup worktree's `.artifacts/check/20261014T184449Z`, a worktree
slated for cleanup), and the figures reproduce from any `wireguard` run
dump on s4 (`capped -- scripts/in-bundle python3 -m evaluator.check
--suite wireguard`, about three minutes on an idle box). The review reran
both probes and reproduced the tables. `scripts/probes/c-fib-shape.py`
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
| `inflate`, `halve`, `replace`, `update_children`, `fib_insert_node`, `fib_insert_alias`, `leaf_new`, `tnode_new` | 0 | 0 | 0 |
| `ip_route_output_key_hash_rcu`, `__mkroute_output` | 19, 23 | 179, 175 | 497, 490 |
| `ip_route_input_slow` | 27 | 31 | 40 |
| `fib_validate_source` (the fast path only; `__fib_validate_source` 0) | 7 | 31 | 40 |
| `udp_v4_early_demux` (no socket found) | 5 | 27 | 36 |
| `fib_create_info`, `fib_find_info`, `fib_nh_init`, `fib_valid_prefsrc` (the early return) | 28, 11, 6, 1 | 4 | 4 |
| `fib_sync_down_dev`, `fib_del_ifaddr`, `fib_magic`, `fib_add_ifaddr` | 18, 19, 6, 5 | 20, 10, 14, 4 | 21, 10, 14, 4 |
| `__inet_dev_addr_type` (all), of which its lookup (:225) | 10 | 189, 16 ops in 10 traces | 300 |
| `arp_constructor` (:242) | 11 | 175 | 198 |
| `rt_cache_flush`, `rt_cache_valid`, `ipv4_dst_check`, `ip_rt_multicast_event` | 1, 2, 2, 1 | 192, 152, 22, 189 | 212, 338, 39, 204 |
| `fib_nh_common_init`, `fib_nexthop_info` (IPv6 callers at `wg_up`) | 4, 7 | 185, 189 | 190, 211 |

The lookup's callers inside the window, from a per-operation query over
the dump (`.tmp`, reproducible from the probe's data): the output route
(497 operations); the input route (40, the `d2_rx_*` and `d3` receive
traces); `arp_constructor`'s classification of a unicast next hop at the
neighbour's creation (6 operations in 4 traces: the `wg_xmit` transmits
of `b1_basic`, `b1_other_endpoint`, `b1_trie_routing`, `b1_v6` to new
destinations; the other 192 `arp_constructor` runs classify the
multicast group at `wg_up` and return early); `fib_del_ifaddr`'s
classification (10: `wg_delete`, `wg_set_mtu 0`, `wg_netns_close`,
`wg_deladdr`). `__inet_bind` (196 operations) and the multicast joins
return early with no lookup; `__ip_dev_find` is covered only on its
found-address arm (devinet.c:159-160, 143 operations), never the
fallback; `fib_compute_spec_dst` only on its `inet_select_addr` line
(:306, 213 operations).

The lookup's shape is exercised: the step-2 prefix test (:1499) in 59
traces, the backtrace loop head (:1522) in 56 (for a `10.0.0.x`
destination the walk descends to the wg0 host route's leaf at index 2 of
the pos-26 node, mismatches, strips `cindex` from 2 to 0 and takes the
`0/0` leaf without climbing: :1522 is evaluated, its body not entered),
the root's `-EAGAIN` (:1529) in 10 (`b1_down`, the `l_delete_*` sends,
`w9_unroutable`, `w9_deladdr_then_send`). The `fib_table_insert` hits are
`l_down_after_session`, `l_down_up_keepalive`, `l_down_up_stale_response`
and `l_up_down_noop`, where the after-down `wg_up`'s `NETDEV_UP` re-adds
the surviving address's local route inside the ioctl and finds its alias
present (the `fa_match` arm, :1256-1262, then `-EEXIST`, which `fib_magic`
ignores): no node is inserted. The boot-time inserts of `lo` and the
`route_into_wg0` requests are outside every window: the guest captures
the task's coverage count at the syscall's return (`harness/guest.c:2534`)
and issues the address and route requests after the wait (`:2586-2601`).
So an insertion of a leaf or a tnode, an inflate, a halve or a `replace`
has never been inside a window. `fib_table_delete` is reached by the W9
`wg_delroute`/`wg_deladdr` operations and `wg_delete`; `fib_table_flush`
and the resize by `wg_down`, `wg_delete`, `wg_set_mtu 0` and the W8 exits.

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
| `fib_semantics.c:1383` (`nh_saddr_genid` vs `dev_addr_genid`) | 73 | 43 | random, equal pairs |
| `ip_route_output_key_hash_rcu:2860` (the route's construction) | 11303 | 59 | |
| `ip_route_input_slow:2289`-`:2440` | 26-80 each | 1-3 | destinations `0x200000a`, `0x302010a`, `0x1feff0a` |

Every choice point of section 8 that the corpus reaches has its operands
in the stream already, so the module's outcome sets and operand sets are
checkable on the existing corpus from the first build, under the set
semantics of section 8; the walk's steps are checked by 9.4 and 10.

### 9.3 The fixture's tables and the trie's shape

From the C alone (1.8 and `route_into_wg0`), the namespace's one trie
holds, after `lo` up and a successful `wg_up`:

| Prefix | Type, scope, table | Origin |
| --- | --- | --- |
| `127.0.0.1/32` | local, host, LOCAL | `fib_add_ifaddr` :1140 for `127.0.0.1/8` |
| `127.0.0.0/8` | local, host, LOCAL | :1155-1158, loopback prefix route |
| `127.255.255.255/32` | broadcast, link, LOCAL | :1161-1164 |
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
core and its first unit test; the exact check is 9.4.

### 9.4 The shape oracle: `/proc/net/fib_trie`

`/proc/net/fib_trie` prints, per table, every tnode as `+-- prefix/len
bits full empty` (the node's prefix length is `KEYLENGTH - pos - bits`)
and every leaf as `|-- key` followed by its aliases as `/plen scope type
[tos=]` in list order (fib_trie.c:2780-2813; the aliased tables print the
one trie twice). The guest reads it outside the window, after the
fixture's setup and after the post-operation wait of every operation
that changes the table (`wg_up`, `wg_down`, `wg_delete`, `wg_deladdr`,
`wg_delroute`, `wg_set_mtu`, `wg_netns_close`, and the corpus's
`wg_addroute`, `wg_addaddr`), and prints it as an observation line; the
harness parses it to a shape, the checker compares it with the mirror's
serialised trie as a new comparison class, exact on node positions,
bits, the full and empty counts, the leaves' keys and the aliases' order,
length, scope and type. A new instrument on the trust surface, so it
gets its one-off mutant (a serialiser that drops `full_children` from a
node; rejected by the comparison), run once in C1 and deleted unless it
replaces a sentinel. The read runs trie code outside the window and adds
nothing to the coverage.

## 10. The corpus

A `routing` directory under `corpus/` with its own suite name, run with
the WireGuard groups at the claim point, and the generator's `routing`
class (`ROUTING_SHARE`, today 0.05) extended with route insertions. The
guest adds, inside the lane: `wg_addroute family dst plen oif type metric
[mtu] [flags]` (`RTM_NEWROUTE` with `NLM_F_CREATE` and optionally `EXCL`,
`REPLACE`, `APPEND`; type unicast, unreachable, blackhole or prohibit;
`oif` wg0 or `lo`; the validator refuses type local, a gateway and a
table other than main), `wg_addaddr addr plen` on wg0 (a second address,
a prefix shorter than 32, for `fib_add_ifaddr`'s prefix and broadcast
routes and `fib_del_ifaddr`'s scan), `wg_delroute` generalised to a
destination, prefix, `oif` and metric, and the `/proc/net/fib_trie` read of
9.4; the harness adds the trace fields, the validator rules and the
generator class.

Traces:

- the insert path with every arm of `fib_table_insert` (`-EEXIST`,
  replace, append, the new leaf, the new tnode, `-ENETDOWN` from
  `fib_check_nh_nongw` on a down device) inside the window, and
  `resize`'s inflate; deletions reaching the delete's match arms and
  `halve`;
- lookups at each depth: transmits to `127.0.0.1`, to `10.255.254.1`, to
  a host route, to an address under `127/8` that is not a leaf (the
  step-2 fallback to the `/8`), to the default, with and without a
  source set;
- the walk's distinguishing set: `wg_addroute 8.0.0.0/5 unreachable`,
  `12.0.0.0/8 via wg0`, `14.0.0.0/8 via wg0`, then transmits to `9.0.0.1`,
  `12.0.0.1`, `13.0.0.1`, `14.0.0.1`. At the pos-26 node `13.0.0.1` has
  index 3, descends into the tnode the two `/8` routes form, mismatches,
  and must backtrack to index 2, where the `/5` leaf (slen 27) matches
  and returns `-EHOSTUNREACH`; a walk that strips `cindex` to 0 instead
  (mutant 1) takes the default and transmits, and a walk that does not
  record `pn` at the pos-26 node (mutant 2) climbs from the root and
  returns `-ENETUNREACH`: three different system-call results;
- a longest-prefix tie: two aliases at one prefix with different metrics
  (the `fib_find_alias` priority order), one with a different DSCP, and a
  second default route (`tb_num_default 2`, `fib_select_default`'s scan
  skipping gateway-less candidates);
- the default route's accessed flag: delete before and after a lookup
  (the existing `w9_delroute_untouched` and `w9_session_delroute_untouched`
  are the pair);
- an insertion sequence of eight `/32` routes under one `/24` and their
  deletion (inflate to four bits, halve back, collapse; `replace` and
  `update_children` with both arms of :462);
- `wg_addaddr` of `10.1.0.1/24` and its deletion: the prefix route, the
  network broadcast `10.1.0.255`, `fib_valid_prefsrc`'s lookup, the
  `fib_del_ifaddr` scan;
- the input side: a decrypted packet to the second address (local), to
  `10.1.0.255` (`RTN_BROADCAST`, `brd_input`, delivered by udp.c's
  broadcast path, outside this module and `unsupported` there), to a
  host route's destination (`-EHOSTUNREACH`, no ICMP), replacing row 13's
  exclusion by decisions; the loopback destinations stay martians before
  the lookup (row 8).

About fourteen handwritten traces and the generator class. IPv6 traces
stay with the environment's rule.

## 11. One-off mutants

Under the set semantics of section 8, a mutant is rejected by a system-
call result, by an outcome set, by an operand set, or by the shape
oracle; each entry says which. Run once, reported in the build's commit,
then deleted, each on the smallest subset:

1. the backtrace's bit strip (`cindex &= cindex - 1` → `cindex = 0`):
   rejected by the distinguishing set's transmit to `13.0.0.1` (a
   transmit instead of `-EHOSTUNREACH`); on today's corpus it survives,
   since every destination strips a one-bit `cindex`;
2. the `slen > pos` record dropped (:1480): rejected by the same transmit
   (`-ENETUNREACH` instead of `-EHOSTUNREACH`);
3. `prefix_mismatch` without the `-prefix` term: results unchanged (the
   alias scan's suffix test catches what the mask would), rejected by the
   outcome set at :1499 in any operation with a mismatch (59 traces);
4. `should_inflate`'s root threshold 30 → 50: rejected by the operand set
   at `resize:869` on the insertion sequence and by the shape oracle;
5. the alias order in `fib_insert_alias` (`tb_id` ascending): rejected by
   the tie trace's result and by the shape oracle's alias order;
6. the accessed-flag condition at `fib_table_delete:1754` dropped:
   rejected by `w9_delroute_untouched` through the dst cache's generation
   (the rule the environment carries by hand today);
7. the shape serialiser dropping `full_children` (9.4): rejected by the
   oracle on every trace;
8. the `fib_sync_down_dev` cut's mutant (5(b)) and the operand exclusions'
   (5(a), 5(c)): a wrong outcome reported at a neighbouring declared
   decision, rejected by control flow.

The sentinel set gains at most two entries (the lookup channel, item 1;
the shape oracle, item 7) if the integration keeps them; the rest are
deleted.

## 12. The proof tree

Files naming the routing environment (`routeLookup`, `route4`, `route6`,
`addrs4`, `defaultRoute4`, `ipv4Gen`, `routesPending`, `wgDelroute`,
`wgDeladdr`), read-only via `git show` at the commits of the first
revision:

- main (ca6b22e): 6 files: `Logged/Operations.lean`, `Logged/Syscalls.lean`,
  `WG/Keypairs/Evolution/Syscalls.lean`, `WG/Keypairs/Frames/{Env,Kernel,WGBase}.lean`;
- `proofs/campaign` (b1ec9e8 then; the branch has moved to 3dec2c3 and
  the count can only have grown): 20 files, the six above plus
  `Framing/{EnvOperations,Kernel,KernelEffects}.lean`,
  `WG/AllowedIps/RoutingSocketFrames.lean`, `WG/Cookies/Frames.lean`,
  `WG/Environment/BatchSource.lean`, `WG/Lifetimes/{EnvBatchAudit,EnvControlsAudit,EnvRemainingCalls,SocketSend,SocketSend4,SyscallDispatchAudit,SyscallsAudit}.lean`,
  `WG/Queues/RxRingSocket.lean`; `SocketSend4.lean` names them fifteen
  times;
- `proofs/campaign-2` (e56156e then; now 32776ca): the same six as main.

The change is of a different kind from a relocation: routing state moves
from `World` to `Kernel`, and every `send4`, batch `xmit` and input lookup
then writes `Kernel` (the alias's accessed bit, the per-nexthop source
cache) where today it writes `World`, so frames of the form "this path
leaves `Kernel` unchanged except ..." change their statements, not only
their proofs. The core's nested inductive (an array of optional
subtrees) costs more than a binary tree in Lean: structural recursion
needs the array's `sizeOf` lemmas or well-founded recursion, and
induction principles are written by hand once. Cost: hours on main and
campaign 2, two to three days on campaign 1 (the `SocketSend4` and
`AllowedIps` frames, the `Kernel` effect frames), under lag-and-repair; a
guess until the change exists.

What campaign 3's routing composition needs from the module, stated as a
requirement on C1's build: the core (`tableLookup`, `tableInsert`,
`tableDelete`, `resize`) is pure and total over the inductive, with no
effect inside it, the lookup returning its result and the accessed
alias's position and the wrapper applying the write, so that the
specification "the lookup returns the longest live prefix whose alias
passes the DSCP, scope and nexthop tests, in the C's order, and marks it
accessed" is a theorem about a function of the trie and the flow; the
trie's well-formedness (keys consistent with `pos` and `bits`, counts
exact, aliases ordered as 1.5) is a predicate the inserts and deletes
preserve, stated with the core; and `send4`'s route, the batch's inner
route, the neighbour classification and the receive predicate's local
decision are each one call of the same function on the namespace's trie,
so the end-to-end relation from a transmit's destination to the receiving
socket composes through it, for IPv4 (section 7). The conventions note's
items apply (properties over a projection, history on the proof side).

## 13. Risks, landings, estimate, decisions

Risks, the stopping one first:

1. The fixture's trie is constructed by the mirror from the C's rules
   with no insertion ever observed, and the existing corpus checks only
   outcome and operand sets per operation. Settled by 9.4: the proc read
   checks the shape exactly from the first run of C1, and the
   distinguishing destinations of section 10 check the walk's steps by
   their results. If the shapes differ at the first run, the difference
   is in the transcription's insert order or a rule of 1.8, found by
   diffing two printed tries; the transcription already matches the
   kernel's recorded node positions (9.3).
2. The three hidden inputs of section 5: (b) needs its treatment decided
   before `fib_semantics.c` is anchored; a wrong treatment shows as a
   rare red in the down and delete traces (about one in 256 by the
   bucket count), which the cut removes exactly.
3. The shared IPv4/IPv6 helpers (section 6) need the per-caller cut before
   `fib_semantics.c` is anchored; without it C2 cannot land.
4. The decision count: about fifteen declared decisions per lookup and
   up to twenty lookups per operation in the send-heavy traces; the
   checker's matching is linear and the operand rows grow by about a
   fifth of today's. Measured at the first claim point.
5. The neighbour set as new environment state: exact on this fixture
   (no collection below 128 entries, removal at down and unregister);
   a trace creating 128 neighbours is `unsupported`.
6. The campaign-1 carry (two to three days) lands while R3's packet
   paths are open; the regime is merge-and-carry, not a prerequisite.
7. The decision at `__mkroute_output`'s cache hit (3.4) is observable
   only through an allocation that is a cut; stated, not modelled.

Landings, each on s4 with its claim point, and what each gives campaign 3:

| Landing | Content | Gives campaign 3 | Days |
| --- | --- | --- | ---: |
| C1 | `fib_trie.c` anchored; the core with `replace` and `update_children`, insert, delete, flush, resize; `fib_info` sharing; the fixture's tables constructed by the C's rules; `World.route4` and the generation bumps replaced; the output route, the input route's lookup and local/unreachable/martian arms, the neighbour classification with the neighbour set, `fib_del_ifaddr`'s classification, `fib_valid_prefsrc` (mirrored, unanchored); hidden input (a) as state with its operand exclusion; the shape oracle with its comparison class; the guest's `wg_addroute`, `wg_addaddr`, `wg_delroute` and proc read; the `routing` corpus and generator class; mutants 1 to 7 | both lookups as one pure function over the trie with the accessed write explicit: the composition's prerequisite | 8 to 10 |
| C2 | `fib_frontend.c` and `fib_semantics.c` anchored with their cut lists; the per-caller cut for the shared helpers; hidden inputs (b) and (c) as a cut and an exclusion; the notifier arms and `fib_select_default` as declared decisions | nothing new for the composition; the frontend's decisions declared | 3 |
| C3 | `route.c` anchored: the output and input sequences as declared decisions, the absolute generation as an operand, the receive rows 5 to 13 as decisions, `ip_error`'s deferral reversed; the remaining flush sites | the input rows as declared decisions | 3 |
| settling, claim points | one per landing | | 1 to 2 |

Fifteen to eighteen agent-days, about 1.6 WU at the plan's rate, against
the plan's "design 1 d, audit 0.5 d, build 6 d", which covered the trie
alone and none of the guest work. The plan's critical-path claim ("C,
about eight days from design to landing") becomes C1 at about ten days
from the design, with C2 and C3 off the critical path. Design: one day
with this revision.

Decisions for the user:

- U1: anchor `fib_frontend.c`, `fib_semantics.c` and `route.c` with cut
  lists in C2 and C3 (recommended, with the per-caller cut for the
  shared helpers), or keep them mirrored but unanchored. Anchoring
  `route.c` revises the boundary decision of 2026-10-07 and reverses the
  `ip_error` deferral of 2026-10-08; the recommendation is to revise
  both, since the lane's purpose is exactly the routing WireGuard's
  observables depend on.
- U2: IPv6 deferred to its own lane (section 7), and campaign 3's
  composition stated for IPv4 in its charter.
- U3: the three-landing order, with C1 first for campaign 3, against one
  landing of the whole.
- U4: the module's home, `Leanux/Net/Fib/` and `Leanux/Net/Route.lean`, a
  new tree beside `FS`, `WG` and `Seccomp`.
- U5: the standing-rule edit U4 implies: AGENTS.md's list of the mirror's
  directories ("the mirror (`Leanux/FS`, `Leanux/WG`, `Leanux/Kernel`,
  `Leanux/Env`, `Leanux/Runner.lean`) carries no theorem") gains
  `Leanux/Net`, and `scripts/proof-gate`'s import check covers it.
- U6: the treatment of hidden input (b): the cut at
  `fib_sync_down_dev:2021` with the mirror walking its own namespace's
  nexthops (recommended), against a record of `hash_mix` that would not
  make the walk exact.

Tactical, the fork's: the pure core with a thin wrapper; `fib_info` as a
map with reference counts; the parent pointer as an explicit path with
the `fresh` mark; the neighbour set in the environment; the corpus list
of section 10; the mutant list of section 11; the shape oracle's format.

[AGENT 2026-10-14] The measurement reads an existing run dump rather
than booting a guest: KCOV instruments every file on this configuration,
so the coverage and comparison streams of any `wireguard` run already
carry the routing code's decisions and operands.

[AGENT 2026-10-14] `resize` is in scope whole: reachable by the lane's
own corpus, its decisions recorded with operands, no profound reason
against.

[AGENT 2026-10-15] The input route's lookup moves into C1 so that the
first landing gives campaign 3 both lookups; the shape oracle is in
scope from C1; the three hidden inputs are treated by two operand
exclusions and one decision cut, no kernel change.

## 14. Review dispositions

[The review](2026-10-15-design-c-review.md) (1cfadd5, a Claude Opus 5.5
reviewer; its trailer names Fable at the coordinator's instruction) has
fifteen findings. Each is fixed in this revision, answered with a reason
the user can check, or raised as a decision.

1. Callers of the lookup inside the window (blocking). Fixed: measured
   per operation (9.1), the four in-window callers are C1 consumers
   (3.2): the output route, the input route, `arp_constructor`'s
   classification with the neighbour set as new environment state, and
   `fib_del_ifaddr`'s; `fib_valid_prefsrc` joins for the corpus's prefix
   routes; `__ip_dev_find`'s fallback and `fib_compute_spec_dst`'s lookup
   are unreachable on this fixture and stay `unsupported`, with the
   reasons; `__inet_bind` and the multicast joins return before the
   lookup. The U1 cut of `__inet_dev_addr_type` is withdrawn (section 6:
   no caller of an anchored function can be a cut). The neighbour
   periodic gc was checked against neighbour.c:980: no collection below
   128 entries, so the set is exact.
2. What C1 gives campaign 3, and the lookup's write (blocking). Fixed:
   the input route's lookup with its local, unreachable and martian
   arms moves into C1 (3.2, section 13), so C1 gives both lookups; the
   plan's critical path is restated (C1 at about ten days, C2 and C3 off
   it); the lookup returns the accessed alias's position and the wrapper
   writes it (3.2, section 12); the interface is stated as a requirement
   on the build.
3. Hidden inputs (blocking for C2). Fixed: section 5 treats (a)
   `dev_addr_genid` as mirror state with an operand exclusion (a record
   at :3665 would not cover the fixture's namespace, whose creation
   precedes the capture; stated), (b) `hash_mix` as a decision cut at the
   walk's skip with the mirror walking its own namespace's nexthops,
   raised as U6 before C2, and (c) the global count as a declared
   decision with excluded operands and a fail-closed rule; "no hidden
   input" and "oracle changes: none" are restated as "none for the trie;
   three in the route paths, treated by instruments with their mutants".
4. The checker's set semantics and the shape oracle. Fixed: section 8
   states the semantics (`check.py:1019-1030`, `:1095-1110`, `:1138-1142`,
   `:1230-1245`) and withdraws "settles"; 9.4 adopts `/proc/net/fib_trie`
   as the exact shape oracle from C1, a new comparison class with its
   mutant (the `RTM_GETROUTE` remedy is withdrawn: it returns routes,
   not the shape); section 10 designs the distinguishing destination set
   (`8.0.0.0/5 unreachable`, `12/8`, `14/8`, the transmit to `13.0.0.1`)
   that mutants 1 and 2 change the system-call result of; section 11
   is rederived with the rejecting instrument named per mutant, and
   mutant 1's survival on today's corpus is stated.
5. The alias order. Fixed: 1.5 has `slen` ascending, `tb_id` descending,
   priority ascending within, with `fib_insert_alias`'s stop conditions
   (:1172-1177) and `fib_remove_alias`'s use of the last alias
   (:1655-1660); 1.6's suffix test is restated as a test on the prefix
   bits above the suffix (:1561).
6. The flush sites and the aliased flush. Fixed: 1.9 lists
   `ip_rt_multicast_event` (189 traces), `nh_netdev_event`'s second flush
   on `NETDEV_CHANGEMTU`, `arp_netdev_event`'s and the devinet sysctls';
   1.1 states the two-pass `fib_flush` over the one trie; 1.8 adds
   `arp_ifdown`; C3 carries the absolute generation as an operand once
   `route.c` is anchored, counting every flush since the namespace's
   creation including the setup's (section 13).
7. `replace` and `update_children`. Fixed: 1.3 and 1.4 describe both with
   the parent-identity test (:462); 3.1 adds the `fresh` mark so the
   mirror reproduces it without pointers; section 8 declares `replace`'s
   full-child test and `update_children`'s two tests, the identity one
   without operands.
8. The shared IPv4/IPv6 helpers and the boundary decision. Fixed and
   raised: section 6 names `fib_nh_common_init`, `fib_nexthop_info` and
   `fib_nh_common_release` with their IPv6 callers and trace counts, and
   proposes the per-caller cut keyed on the outermost frame, built in C2
   before anchoring, as the mechanism (keeping the file unanchored is
   the alternative); U1 states that anchoring `route.c` revises the
   [USER 2026-10-07] boundary decision and reverses the [AGENT 2026-10-08]
   `ip_error` deferral.
9. The allocation sites. Fixed: section 5 has `:333` (the `vzalloc` at
   :335 is not a slab call and needs more than 511 children), `:1281`,
   `:1344`, `ip_fib_metrics_init`'s `kzalloc` (metrics.c:74-76), and
   `fib_nh_common_init`'s per-cpu allocation as lax and unsteerable
   (the `dstCacheInit` precedent); the in-window allocations of the four
   insert traces are noted.
10. The input side. Fixed: 1.9 gives `ip_route_input_slow`'s order with
    `!in_dev`, the early demux (which finds no connected socket on this
    fixture), `ip_route_input_rcu`'s multicast branch and
    `fib_has_custom_local_routes`; the corpus's broadcast case uses the
    network broadcast of the `wg_addaddr` prefix, and the loopback
    destinations stay martians before the lookup; the custom local route
    is refused by the validator (fail-noisy).
11. The harness work and the estimate. Fixed: section 10 names the guest
    operations and the harness items; section 13 re-plans the landings
    with the C1 task list and estimates fifteen to eighteen days, C1 at
    eight to ten, above the review's fifteen to twenty's lower bound and
    its C1 range, because the input route and the shape oracle are now in
    C1.
12. The proof carry. Fixed: section 12 states the change in kind (writes
    to `Kernel`), the nested inductive's cost, the moved branch heads, and
    the estimate as a guess.
13. The probe figures. Fixed: the four insert traces named; the pos-26
    backtrace described as a strip without a climb; the 9.3 and probe
    citations corrected to :1155-1158 and :1161-1164; the flush's lines
    to :2041 and :2044; `fib_select_default`'s decisions added to section
    8 (C2); the `&& max_work` terms declared unwitnessed; the dump's
    location and the rerun command stated.
14. IPv6 and the composition's scope. Fixed: section 7 and U2 state that
    campaign 3's composition is an IPv4 result for its charter; the IPv6
    insertions at `wg_up` are finding 8's shared-helper case.
15. The standing rule. Raised: U5, the AGENTS.md mirror-directory list and
    the proof gate's import check.

The probe's labels in `scripts/probes/c-fib-shape.py` are corrected with
this revision (finding 13).
