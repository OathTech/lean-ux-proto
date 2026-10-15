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
    let some fi := (← getK).fib4.infos.get? res.info | invariant "ip_route_output: an alias without its info"
    if res.type == .local then
      -- :2833-2841: the prefsrc or the destination; the loopback device
      if saddr == 0 then saddr := if fi.prefsrc != 0 then fi.prefsrc else daddr
      return .ok { dev := LO_IFINDEX, src := saddr, mtu := fi.mtu }
    -- :2855-2857: `fib_select_path` (a single path, the source when none) and the device
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

/-- The neighbour constructor's address classification at a next hop's
    first use on `dev` (`ip_finish_output2` → `__neigh_create` →
    `arp_constructor`, arp.c:242: `inet_addr_type_dev_table`), recorded in
    the environment's neighbour set; nothing for an existing entry. -/
def neighbourClassify (dev nexthop : Nat) : M Unit := do
  let w ← get
  if w.neighbours.any (fun (d, a, _) => d == dev && a == nexthop) then return
  let t ← inetDevAddrType (some dev) nexthop
  modify fun w => { w with neighbours := w.neighbours ++ [(dev, nexthop, t.code)] }

end Leanux.Net
