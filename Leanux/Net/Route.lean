import Leanux.Net.Fib.Table

/-!
# The routes WireGuard's paths read (net/ipv4/route.c, fib_frontend.c)

Lane C (docs/2026-10-15-design-c-fib-trie.md, 3.2 and section 4): the
output route of `ip_route_output_key_hash_rcu` (route.c:2696-2864), the
input route of `ip_route_input_slow` (:2265-2477) as far as the receive
predicate reads it, and the neighbour constructor's address classification
(arp.c:242). `route.c` is mirrored unanchored in this landing: its choice
points are plain tests in the C's order; the trie's decisions inside the
lookups are declared. IPv6 keeps the environment's rule (`World.route6`).
-/

namespace Leanux.Net

open Leanux
open Leanux.Net.Fib

/-- `fib_select_default(flp, res)` (fib_semantics.c:1868-1935): the scan over
    the leaf's default aliases for a live gateway route to prefer. None of
    this fixture's routes has a gateway (`wg_addroute` takes none), so every
    candidate that reaches :1904 is skipped at `!nhc->nhc_gw_family` and
    the result stands; the scan's earlier tests are the C's, in order. -/
def fibSelectDefault (res : Result) : M Unit := do
  let leaf ← nodeAt res.leaf
  let some first := (← getTable).infos.get? res.info | invariant "fib_select_default: an alias without its info"
  let mut lastPrio := first.priority
  let mut lastDscp := 0
  for fa in leaf.aliases do
    let some fi := (← getTable).infos.get? fa.info | invariant "fib_select_default: an alias without its info"
    if fa.slen != KEYLENGTH - res.prefixlen then continue
    if fa.dscp != 0 then continue   -- `fib_dscp_masked_match` on a zero-DSCP flow
    if fa.tbId != res.tbId then continue
    if fi.priority > lastPrio && fa.dscp == lastDscp then
      if lastDscp != 0 then continue
      break
    if fi.flags &&& RTNH_F_DEAD != 0 then continue
    lastDscp := fa.dscp
    lastPrio := fi.priority
    if fi.scope != RT_SCOPE_LINK || fi.type != .unicast then continue
    -- :1904: `!nhc->nhc_gw_family`: no route here has a gateway
    continue

/-- `ip_route_output_key_hash_rcu(net, fl4, res, skb)` (route.c:2696-2864) for
    the flows WireGuard's sockets and the fixture's sender build: no `oif`,
    no mark, scope universe, a destination always set. The source test at
    :2751-2754 is `__ip_dev_find` (devinet.c:153-180): an interface address,
    or the local table's `RTN_LOCAL` route for it (unreachable on this
    fixture: a source that is not an interface address never reaches here). -/
def routeOutput4 (saddr daddr : Nat) : M (Except Int Route) := do
  let mut saddr := saddr
  if saddr != 0 then
    -- :2706-2712: a multicast, limited-broadcast or zeronet source
    if saddr / 2 ^ 28 == 0xe || saddr == 0xffffffff || saddr / 2 ^ 24 == 0 then return .error (-22)
    -- :2751-2754: `__ip_dev_find(net, fl4->saddr, false)`
    if !(← inetLookupIfaddr saddr) then
      -- the local table's lookup for a non-interface local address
      unsupported "an output route from a source that is not an interface address (__ip_dev_find's lookup)"
  -- no `flowi4_oif`; `fl4->daddr` is set
  match ← tableLookup { daddr, scope := RT_SCOPE_UNIVERSE } with
  | .error err =>
    -- `fib_lookup` maps -EAGAIN to -ENETUNREACH (ip_fib.h:325-326); no oif
    return .error (if err == -11 then -101 else err)
  | .ok res =>
    let some fi := (← getTable).infos.get? res.info | invariant "ip_route_output: an alias without its info"
    if res.type == .local then
      -- :2833-2841: the prefsrc or the destination; the loopback device
      if saddr == 0 then saddr := if fi.prefsrc != 0 then fi.prefsrc else daddr
      return .ok { dev := LO_IFINDEX, src := saddr, mtu := fi.mtu }
    -- :2855-2857: `fib_select_path` (fib_semantics.c:2269-2300): no oif, a
    -- single path; a default route in a table with more than one goes
    -- through `fib_select_default`; the source when none
    if res.prefixlen == 0 && (← numDefault res.tbId) > 1 && res.type == .unicast then
      fibSelectDefault res
    if saddr == 0 then saddr ← resultPrefsrc res.info
    -- __mkroute_output (:2545-2665): `IN_DEV_ROUTE_LOCALNET` off, so a loopback
    -- source on a non-loopback device is -EINVAL (:2558-2562)
    if saddr / 2 ^ 24 == 127 && fi.dev != LO_IFINDEX then return .error (-22)
    return .ok { dev := fi.dev, src := saddr, mtu := fi.mtu }

/-- `routeLookup family saddr daddr`: the fixture's output route, IPv4 on the
    trie, IPv6 on the environment's rule. -/
def routeLookup (family saddr daddr : Nat) : M (Except Int Route) := do
  if family == 4 then routeOutput4 saddr daddr
  else return (← get).route6 saddr daddr

/-- `ip_route_input_slow`'s verdict for the decrypted packet's addresses, as
    the receive predicate reads it (the design note, 1.9): the martian tests
    before the lookup are the predicate's rows; after the lookup, a local
    delivery, a miss (`-EHOSTUNREACH` with forwarding off), a broadcast
    (`brd_input`), or a forward or other type the stack refuses. -/
inductive InputVerdict where
  | local (srcInvalid : Bool)
  | noRoute
  | broadcast
  | notLocal
  deriving Repr, BEq

/-- The lookup of `ip_route_input_slow` (:2347-2376) and `fib_validate_source`'s
    fast path on this configuration (fib_frontend.c:421-451): a local source
    is `-EINVAL`, anything else passes with no lookup. -/
def routeInput4 (saddr daddr : Nat) : M InputVerdict := do
  match ← tableLookup { daddr, scope := RT_SCOPE_UNIVERSE } with
  | .error _ => return .noRoute   -- `-EHOSTUNREACH`: `!IN_DEV_FORWARD(in_dev)` (:2348-2352)
  | .ok res =>
    if res.type == .broadcast then return .broadcast
    if res.type == .local then
      -- `fib_validate_source`: `rp_filter` 0, no custom local routes, so
      -- `inet_lookup_ifaddr_rcu(src)` decides (:442-443)
      return .local (← inetLookupIfaddr saddr)
    -- `!IN_DEV_FORWARD(in_dev)`: `-EHOSTUNREACH` for a unicast route; another
    -- type is a martian destination
    return .notLocal

/-- `ip_finish_output2`'s neighbour for a packet on `dev` (`ip_neigh_gw4` →
    `__ipv4_neigh_lookup_noref`, arp.h:38-44): on a loopback or
    point-to-point device (every device of this fixture: lo, wg0) the key is
    `INADDR_ANY`, one neighbour per device, created at the device's first
    output and classified by `arp_constructor` (arp.c:233-242) as
    `inet_addr_type_dev_table(net, dev, 0)`: the zeronet early return
    (fib_frontend.c:215), no lookup. Nothing for an existing entry. -/
def neighbourClassify (dev : Nat) : M Unit := do
  let w ← get
  let ns := w.fibCreatorNs
  if w.neighbours.any (fun (n, d, _) => n == ns && d == dev) then return
  let t ← inetDevAddrType (some dev) 0
  modify fun w => { w with neighbours := w.neighbours ++ [(ns, dev, t.code)] }

end Leanux.Net
