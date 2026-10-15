import Leanux.Net.Fib.Core

/-!
# The IPv4 FIB table: fib_info, insert, delete, flush, and the frontend's
# sequences (net/ipv4/fib_semantics.c, fib_frontend.c)

Lane C (docs/2026-10-15-design-c-fib-trie.md, 3.2). `fib_trie.c` is anchored
in this landing and its decisions are declared (`Core.lean`); the functions
of `fib_semantics.c` and `fib_frontend.c` here are mirrored unanchored (C2
anchors them with their cut lists), so their choice points are plain tests
in the C's order and only the trie's decisions are reported.
-/

namespace Leanux.Net.Fib

open Leanux

/-- `NLM_F_*` (netlink.h). -/
abbrev NLM_F_REPLACE : Nat := 0x100
abbrev NLM_F_EXCL : Nat := 0x200
abbrev NLM_F_CREATE : Nat := 0x400
abbrev NLM_F_APPEND : Nat := 0x800

/-- `struct fib_config` as the paths here read it (fib_frontend.c:727-862,
    `fib_magic` :1083-1121). `dst` is the host-order key. -/
structure Config where
  dst : Nat := 0
  dstLen : Nat := 0
  dscp : Nat := 0
  table : Nat := RT_TABLE_MAIN
  protocol : Nat := 0
  scope : Nat := RT_SCOPE_NOWHERE
  type : RouteType := .unspec
  flags : Nat := 0
  prefsrc : Nat := 0
  oif : Nat := 0
  priority : Nat := 0
  /-- `RTAX_MTU` of `RTA_METRICS`; 0 when absent. -/
  mtu : Nat := 0
  nlflags : Nat := 0
  deriving Repr, Inhabited

abbrev LO_IFINDEX : Nat := Leanux.LO_IFINDEX
abbrev WG0_IFINDEX : Nat := Leanux.WG0_IFINDEX

/-- `rt_cache_flush(net)`: `rt_genid_bump_ipv4` (route.c:406-409). -/
def rtCacheFlush : M Unit := modifyTable fun tb => { tb with rtGenid4 := tb.rtGenid4 + 1 }

/-- `atomic_inc(&net->ipv4.dev_addr_genid)` (fib_frontend.c:1458, :1463, :1505). -/
def devAddrGenidBump : M Unit := modifyTable fun tb => { tb with devAddrGenid := tb.devAddrGenid + 1 }

/-- Whether a device's IPv4 `in_device` exists and the device is up, from
    the environment: `lo` always; wg0 while its `inet4Dev` holds (W4) and
    it runs. The addresses of a device: `lo`'s `127.0.0.1` (scope host),
    wg0's `World.addrs4` (scope universe). -/
def deviceUp (dev : Nat) : M Bool := do
  if dev == LO_IFINDEX then return true
  if dev == WG0_IFINDEX then
    match (← getK).wg with
    | some d => return d.running
    | none => return false
  return false

def deviceHasInet (dev : Nat) : M Bool := do
  if dev == LO_IFINDEX then return true
  if dev == WG0_IFINDEX then
    match (← getK).wg with
    | some d => return d.inet4Dev
    | none => return false
  return false

/-- A device's addresses with their scopes (devinet's `ifa_list`). -/
def deviceAddrs (dev : Nat) : M (List (Nat × Nat)) := do
  if dev == LO_IFINDEX then return [(LOOPBACK4, RT_SCOPE_HOST)]
  if dev == WG0_IFINDEX then return (← get).addrs4.map (·, RT_SCOPE_UNIVERSE)
  return []

/-- `inet_select_addr(dev, dst, scope)` (devinet.c:1356-1413) with no
    destination: the device's first primary address whose scope is within
    `scope`; with none, the scan of the other devices finds `lo`'s
    `127.0.0.1` only for a scope of host or wider. -/
def inetSelectAddr (dev : Nat) (scope : Nat) : M Nat := do
  for (a, s) in ← deviceAddrs dev do
    if s ≤ scope then return a
  if scope ≥ RT_SCOPE_HOST then return LOOPBACK4
  return 0

/-- `inet_lookup_ifaddr_rcu(net, addr)` (devinet.c:186-195): an interface
    address in the namespace, on any device. -/
def inetLookupIfaddr (addr : Nat) : M Bool := do
  if addr == LOOPBACK4 then return true
  return (← get).addrs4.contains addr

/-- `__inet_dev_addr_type(net, dev, addr, tb_id)` (fib_frontend.c:206-234):
    the early returns, then a lookup of the local table. `dev` is `none` for
    `inet_addr_type_table`. -/
def inetDevAddrType (dev : Option Nat) (addr : Nat) : M RouteType := do
  if addr / 2 ^ 24 == 0 || addr == 0xffffffff then return .broadcast
  if addr / 2 ^ 28 == 0xe then return .multicast
  -- `fib_get_table(net, tb_id)` always exists; `ret = RTN_UNICAST`
  match ← tableLookup { daddr := addr, scope := RT_SCOPE_UNIVERSE } with
  | .ok res =>
    let some fi := (← getTable).infos.get? res.info | invariant "address type: an alias without its info"
    match dev with
    | none => return res.type
    | some d => return if d == fi.dev then res.type else .unicast
  | .error _ => return .unicast

/-- `fib_find_info(nfi)` (fib_semantics.c:409-437). -/
def findInfo (fi : FibInfo) : M (Option FibInfoId) := do
  for (id, other) in (← getTable).infos do
    if other.sameIdentity fi then return some id
  return none

/-- `fib_release_info(fi)` (fib_semantics.c:261-285): at the last tree
    reference the info is unhashed and `fib_dead`; nothing else holds it on
    these paths, so the map drops it. -/
def releaseInfo (id : FibInfoId) : M Unit := do
  let some fi := (← getTable).infos.get? id | invariant "fib_release_info: no such info"
  if fi.treeref ≤ 1 then
    modifyK fun k => { k with fib4 := { k.fib4 with infos := k.fib4.infos.erase id } }
  else
    modifyK fun k => { k with fib4 := { k.fib4 with infos := k.fib4.infos.insert id { fi with treeref := fi.treeref - 1 } } }

def modifyInfo (id : FibInfoId) (f : FibInfo → FibInfo) : M Unit := do
  let some fi := (← getTable).infos.get? id | invariant "no such fib_info"
  modifyK fun k => { k with fib4 := { k.fib4 with infos := k.fib4.infos.insert id (f fi) } }

/-- `fib_valid_prefsrc(cfg, fib_prefsrc)` (fib_semantics.c:1391-1412). -/
def validPrefsrc (cfg : Config) (prefsrc : Nat) : M Bool := do
  if cfg.type != .local || cfg.dst == 0 || prefsrc != cfg.dst then
    let tbId := if cfg.table == RT_TABLE_MAIN then RT_TABLE_LOCAL else cfg.table
    let rc ← inetDevAddrType none prefsrc
    let rc ← if rc != .local && tbId != RT_TABLE_LOCAL then inetDevAddrType none prefsrc else pure rc
    if rc != .local then return false
  return true

/-- `fib_create_info(cfg, extack)` (fib_semantics.c:1415-1660) for a single
    nexthop without a gateway: the validations, the allocations, the
    nexthop's device and scope, the prefsrc check, the source selection
    and `fib_find_info`'s sharing. Returns the info's id or the error. -/
def createInfo (cfg : Config) : M (Except Int FibInfoId) := do
  if cfg.type.minScope > cfg.scope then return .error (-22)   -- "Invalid scope"
  if cfg.flags &&& (RTNH_F_DEAD ||| RTNH_F_LINKDOWN) != 0 then return .error (-22)
  -- `fib_info_cnt >= fib_info_hash_size`: the global count (the design
  -- note, 5(c)): the hash does not grow during a trace
  if !(← envOk .fibInfoAlloc) then return .error (-105)   -- -ENOBUFS
  if cfg.mtu != 0 then
    if !(← envOk .fibMetricsAlloc) then return .error (-12)   -- ip_fib_metrics_init's -ENOMEM
  let mut fi : FibInfo := { protocol := cfg.protocol, scope := cfg.scope, flags := cfg.flags,
                            priority := cfg.priority, prefsrc := cfg.prefsrc, type := cfg.type,
                            tbId := cfg.table, mtu := cfg.mtu, oif := cfg.oif, nhFlags := cfg.flags }
  -- `fib_nh_init`: the per-cpu output cache (lax, unsteerable), the oif and flags
  if cfg.type.error != 0 then
    if cfg.oif != 0 then return .error (-22)   -- "Gateway, device and multipath can not be specified"
    -- goto link_it
  else
    match cfg.type with
    | .unicast | .local | .broadcast | .anycast | .multicast => pure ()
    | _ => return .error (-22)   -- "Invalid route type"
    if cfg.scope > RT_SCOPE_HOST then return .error (-22)
    if cfg.scope == RT_SCOPE_HOST then
      -- `nh->fib_nh_scope = RT_SCOPE_NOWHERE; nh->fib_nh_dev = dev_get_by_index(net, oif)`
      fi := { fi with nhScope := RT_SCOPE_NOWHERE }
      if cfg.oif != LO_IFINDEX && cfg.oif != WG0_IFINDEX then return .error (-19)   -- -ENODEV
      if cfg.oif == WG0_IFINDEX && (← getK).wg.isNone then return .error (-19)
      fi := { fi with dev := cfg.oif }
    else
      -- `fib_check_nh` → `fib_check_nh_nongw` (:1244-1275)
      if cfg.flags &&& (2 ||| 4) != 0 then return .error (-22)   -- PERVASIVE, ONLINK
      if !(← deviceHasInet cfg.oif) then return .error (-19)   -- `inetdev_by_index`
      if !(← deviceUp cfg.oif) then return .error (-100)   -- -ENETDOWN
      fi := { fi with dev := cfg.oif, nhScope := RT_SCOPE_HOST }
      -- `!netif_carrier_ok`: wg0's carrier is on while it runs, lo's always
    if fi.prefsrc != 0 && !(← validPrefsrc cfg fi.prefsrc) then return .error (-22)
    -- `fib_info_update_nhc_saddr(net, nhc, fi->fib_scope)` (:1354-1369)
    let saddr ← inetSelectAddr fi.dev fi.scope
    fi := { fi with nhSaddr := saddr, nhSaddrGenid := (← getTable).devAddrGenid }
  -- link_it: the sharing
  match ← findInfo fi with
  | some id =>
    modifyInfo id fun o => { o with treeref := o.treeref + 1 }
    return .ok id
  | none =>
    let id := (← getTable).nextInfo
    modifyTable fun tb => { tb with infos := tb.infos.insert id fi, nextInfo := id + 1 }
    return .ok id

/-- `fib_result_prefsrc(net, res)` (fib_semantics.c:1372-1388): the info's
    prefsrc, else the nexthop's cached source while the generation holds,
    else a fresh selection cached with the generation. The comparison's
    operands are excluded (the design note, 5(a)). -/
def resultPrefsrc (info : FibInfoId) : M Nat := do
  let some fi := (← getTable).infos.get? info | invariant "fib_result_prefsrc: no such info"
  if fi.prefsrc != 0 then return fi.prefsrc
  if fi.nhSaddrGenid == (← getTable).devAddrGenid then return fi.nhSaddr
  let saddr ← inetSelectAddr fi.dev fi.scope
  let genid := (← getTable).devAddrGenid
  modifyInfo info fun o => { o with nhSaddr := saddr, nhSaddrGenid := genid }
  return saddr

/-- `fib_nh_match(net, cfg, fi)` (fib_semantics.c:907-1000) for the fixture's
    gateway-less single nexthop: the priority, then `oif`. -/
def nhMatch (cfg : Config) (fi : FibInfo) : Bool :=
  if cfg.priority != 0 && cfg.priority != fi.priority then false
  else if cfg.oif != 0 && cfg.oif != fi.oif then false
  else true

/-- `fib_metrics_match(cfg, fi)` (fib_semantics.c:1040-1072): without
    `RTA_METRICS` in the request it is true; with one, the values match. -/
def metricsMatch (cfg : Config) (fi : FibInfo) : Bool :=
  cfg.mtu == 0 || cfg.mtu == fi.mtu

def numDefault (tbId : Nat) : M Nat := do
  let t ← getTable
  return if tbId == RT_TABLE_LOCAL then t.numDefaultLocal else t.numDefaultMain

def modifyNumDefault (tbId : Nat) (f : Nat → Nat) : M Unit := modifyTable fun tb =>
  if tbId == RT_TABLE_LOCAL then { tb with numDefaultLocal := f tb.numDefaultLocal }
  else { tb with numDefaultMain := f tb.numDefaultMain }

/-- `fib_table_insert(net, tb, cfg, extack)` (fib_trie.c:1200-1398). -/
def tableInsert (cfg : Config) : M Int := do
  let tbId := cfg.table
  let key := cfg.dst
  let plen := cfg.dstLen
  let slen := KEYLENGTH - plen
  let fiR ← createInfo cfg
  if ← branch .ftiInfoErr (match fiR with | .error _ => true | .ok _ => false) then
    let .error e := fiR | invariant "fib_table_insert: unreachable"
    return e
  let .ok fi := fiR | invariant "fib_table_insert: unreachable"
  let fiPrio : Nat := ((← getTable).infos.get? fi).map (·.priority) |>.getD 0
  let dscp := cfg.dscp
  let (tpPath, leaf) ← findNode key
  let lPath := leaf.map (·.1)
  let aliases := leaf.map (·.2.aliases)
  -- `fa = l ? fib_find_alias(...) : NULL`
  let mut fa : Option Nat := none
  if ← branch .ftiLeaf leaf.isSome then
    fa ← findAlias aliases slen dscp fiPrio tbId false
  -- the release of the info on every `out` path
  let out (err : Int) : M Int := do
    releaseInfo fi
    return err
  let mut err : Int := 0
  let mut faFirst := fa
  let mut existing := false
  if ← branch .ftiHasAlias fa.isSome then
    let some faIdx := fa | invariant "fib_table_insert: unreachable"
    let some fas := aliases | invariant "fib_table_insert: unreachable"
    let faE := fas[faIdx]!
    let faPrio : Nat := ((← getTable).infos.get? faE.info).map (·.priority) |>.getD 0
    if ← branchCmp .ftiDscpEq (faE.dscp == dscp) faE.dscp dscp then
      if ← branchCmp .ftiPrioEq (faPrio == fiPrio) faPrio fiPrio then existing := true
  if existing then
    let some faIdx := fa | invariant "fib_table_insert: unreachable"
    let some fas := aliases | invariant "fib_table_insert: unreachable"
    err := -17   -- -EEXIST
    if ← branchCmp .ftiExcl (cfg.nlflags &&& NLM_F_EXCL != 0) (cfg.nlflags &&& NLM_F_EXCL) 0 then return ← out err
    -- the match loop from `fa` on
    let mut faMatch : Option Nat := none
    faFirst := fa
    let mut i : Nat := faIdx
    for a in fas.drop faIdx do
      _ ← branch .ftiMatchIterate true
      let aPrio : Nat := ((← getTable).infos.get? a.info).map (·.priority) |>.getD 0
      let mut brk := false
      if ← branchCmp .ftiMatchSlen (a.slen != slen) a.slen slen then brk := true
      else if ← branchCmp .ftiMatchTb (a.tbId != tbId) a.tbId tbId then brk := true
      else if ← branchCmp .ftiMatchDscp (a.dscp != dscp) a.dscp dscp then brk := true
      if brk then break
      if ← branchCmp .ftiMatchPrio (aPrio != fiPrio) aPrio fiPrio then break
      if ← branchCmp .ftiMatchType (a.type == cfg.type) a.type.code cfg.type.code then
        if ← branch .ftiMatchInfo (a.info == fi) then
          faMatch := some i
          break
      i := i + 1
    if ← branchCmp .ftiReplace (cfg.nlflags &&& NLM_F_REPLACE != 0) (cfg.nlflags &&& NLM_F_REPLACE) 0 then
      -- `fa = fa_first`
      if ← branch .ftiReplaceMatch faMatch.isSome then
        if ← branch .ftiReplaceSame (faMatch == faFirst) then err := 0
        return ← out err
      err := -105   -- -ENOBUFS
      if ← branch .ftiReplaceNoAlias !(← envOk .fibAliasAlloc) then return ← out err
      let some fIdx := faFirst | invariant "fib_table_insert: unreachable"
      let old := fas[fIdx]!
      let newFa : FibAlias := { slen := old.slen, tbId, dscp := old.dscp, type := cfg.type,
                                accessed := false, info := fi }
      let some lp := lPath | invariant "fib_table_insert: unreachable"
      let leafNode ← nodeAt lp
      setNode lp (some (leafNode.withAliases (fas.set fIdx newFa)))
      -- `if (fib_find_alias(&l->leaf, fa->fa_slen, 0, 0, tb->tb_id, true) == new_fa)` notifiers
      let first ← findAlias (some (fas.set fIdx newFa)) old.slen 0 0 tbId true
      if ← branch .ftiReplaceFirst (first == some fIdx) then
        if ← branch .ftiReplaceNotifyErr false then invariant "fib_table_insert: a notifier error"
      -- `alias_free_mem_rcu(fa); fib_release_info(fi_drop);`
      releaseInfo old.info
      if ← branch .ftiReplaceAccessed old.accessed then rtCacheFlush
      return 0   -- succeeded
    if ← branch .ftiMatch faMatch.isSome then return ← out err
    if ← branch .ftiAppend (cfg.nlflags &&& NLM_F_APPEND != 0) then pure ()
    else fa := faFirst
  err := -2   -- -ENOENT
  if ← branch .ftiCreate (cfg.nlflags &&& NLM_F_CREATE == 0) then return ← out err
  err := -105
  if ← branch .ftiNoAlias !(← envOk .fibAliasAlloc) then return ← out err
  let newFa : FibAlias := { slen, tbId, dscp, type := cfg.type, accessed := false, info := fi }
  let r ← insertAlias tpPath lPath newFa fa key
  if ← branch .ftiInsertErr (r != 0) then return ← out r
  -- `l = l ? l : fib_find_node(t, &tp, key);`
  let lp ← match lPath with
    | some lp => pure (some lp)
    | none => do
      let (_, leaf') ← findNode key
      pure (leaf'.map (·.1))
  if ← branch .ftiNoLeaf lp.isNone then invariant "fib_table_insert: the alias was inserted but its leaf is not found"
  let some lp := lp | invariant "fib_table_insert: unreachable"
  let leafNode ← nodeAt lp
  let idx := leafNode.aliases.findIdx? (fun a => a.slen == slen && a.tbId == tbId && a.dscp == dscp && a.info == fi && a.type == cfg.type)
  let first ← findAlias (some leafNode.aliases) slen 0 0 tbId true
  if ← branch .ftiFirst (first.isSome && first == idx) then
    if ← branch .ftiNotifyErr false then invariant "fib_table_insert: a notifier error"
  if ← branch .ftiDefault (plen == 0) then modifyNumDefault tbId (· + 1)
  rtCacheFlush
  return 0

/-- `fib_notify_alias_delete(net, key, fah, fa_to_delete, extack)`
    (fib_trie.c:1663-1691): the notifier chain is below the cut; the
    `fib_find_alias` call and the two tests are the C's. -/
def notifyAliasDelete (aliases : List FibAlias) (index : Nat) : M Unit := do
  let fa := aliases[index]!
  let first ← findAlias (some aliases) fa.slen 0 0 fa.tbId true
  if ← branch .fnaNotFirst (first != some index) then return
  let next := aliases[index + 1]?
  if ← branch .fnaHasNext next.isSome then
    let some n := next | invariant "fib_notify_alias_delete: unreachable"
    if ← branchCmp .fnaNextSlen (n.slen == fa.slen) n.slen fa.slen then
      if ← branchCmp .fnaNextTb (n.tbId == fa.tbId) n.tbId fa.tbId then pure ()   -- FIB_EVENT_ENTRY_REPLACE
  -- else FIB_EVENT_ENTRY_DEL; `call_fib_entry_notifiers`: no listener

/-- `fib_table_delete(net, tb, cfg, extack)` (fib_trie.c:1694-1759). -/
def tableDelete (cfg : Config) : M Int := do
  let tbId := cfg.table
  let key := cfg.dst
  let plen := cfg.dstLen
  let slen := KEYLENGTH - plen
  let (tpPath, leaf) ← findNode key
  if ← branch .ftdNoLeaf leaf.isNone then return -3   -- -ESRCH
  let some (lPath, leafNode) := leaf | invariant "fib_table_delete: unreachable"
  let fas := leafNode.aliases
  let dscp := cfg.dscp
  let fa ← findAlias (some fas) slen dscp 0 tbId false
  if ← branch .ftdNoAlias fa.isNone then return -3
  let some faIdx := fa | invariant "fib_table_delete: unreachable"
  let mut toDelete : Option Nat := none
  let mut i : Nat := faIdx
  for a in fas.drop faIdx do
    _ ← branch .ftdIterate true
    let some fi := (← getTable).infos.get? a.info | invariant "fib_table_delete: an alias without its info"
    let mut brk := false
    if ← branchCmp .ftdSlen (a.slen != slen) a.slen slen then brk := true
    else if ← branchCmp .ftdTb (a.tbId != tbId) a.tbId tbId then brk := true
    else if ← branchCmp .ftdDscp (a.dscp != dscp) a.dscp dscp then brk := true
    if brk then break
    -- the conjunction of :1728-1736, each operand in order
    let mut ok := true
    if ← branchCmp .ftdTypeZero (cfg.type.code == 0) cfg.type.code 0 then pure ()
    else if !(← branchCmp .ftdTypeEq (a.type == cfg.type) a.type.code cfg.type.code) then ok := false
    if ok then
      if ← branch .ftdScopeNowhere (cfg.scope == RT_SCOPE_NOWHERE) then pure ()
      else if !(← branchCmp .ftdScopeEq (fi.scope == cfg.scope) fi.scope cfg.scope) then ok := false
    if ok then
      if ← branchCmp .ftdPrefsrcZero (cfg.prefsrc == 0) cfg.prefsrc 0 then pure ()
      else if !(← branchCmp .ftdPrefsrcEq (fi.prefsrc == cfg.prefsrc) fi.prefsrc cfg.prefsrc) then ok := false
    if ok then
      if ← branchCmp .ftdProtocolZero (cfg.protocol == 0) cfg.protocol 0 then pure ()
      else if !(← branchCmp .ftdProtocolEq (fi.protocol == cfg.protocol) fi.protocol cfg.protocol) then ok := false
    if ok then
      let m : Nat := if nhMatch cfg fi then 0 else 1
      if !(← branchCmp .ftdNhMatch (m == 0) m 0) then ok := false
    if ok then
      let m : Nat := if metricsMatch cfg fi then 1 else 0
      if !(← branchCmp .ftdMetricsMatch (m != 0) m 0) then ok := false
    if ok then
      toDelete := some i
      break
    i := i + 1
  if ← branch .ftdNotFound toDelete.isNone then return -3
  let some dIdx := toDelete | invariant "fib_table_delete: unreachable"
  let old := fas[dIdx]!
  notifyAliasDelete fas dIdx   -- rtmsg_fib: below the cut
  if ← branchCmp .ftdDefault (plen == 0) plen 0 then modifyNumDefault tbId (· - 1)
  removeAlias tpPath lPath dIdx
  if ← branchCmp .ftdAccessed old.accessed (if old.accessed then 1 else 0) 0 then rtCacheFlush
  releaseInfo old.info
  return 0

/-- `fib_table_flush(net, tb, flush_all)` (fib_trie.c:2006-2093): the walk in
    reverse over the trie, removing the aliases of `tbId` whose info is dead
    (or every alias with `flush_all`), resizing every node on the way up.
    Returns `found`. -/
def tableFlush (tbId : Nat) (flushAll : Bool) : M Nat := do
  let mut pnPath : Path := []
  let mut cindex : Nat := 1
  let mut found : Nat := 0
  for _ in [0:65536] do
    let pn ← nodeAt pnPath
    -- `if (!(cindex--))`
    let was : Nat := cindex
    cindex := if cindex == 0 then 0 else cindex - 1
    if ← branchCmp .ftfClimb (was == 0) was 0 then
      let pkey := pn.key
      if ← branchCmp .ftfRoot pn.isTrie pn.pos KEYLENGTH then break
      if ← branchCmp .ftfSuffix (pn.slen > pn.pos) pn.slen pn.pos then
        setNode pnPath (some (← updateSuffix pn))
      -- `pn = resize(t, pn)`: the parent, with the node resized in it
      let some myIndex := pnPath.getLast? | invariant "fib_table_flush: the root is not a child"
      let parentPath := pnPath.dropLast
      let parent ← nodeAt parentPath
      let parent' ← resizeAt RESIZE_FUEL parent myIndex
      setNode parentPath (some parent')
      setTrie { (← getTrie) with root := (← getTrie).root.map (clearFresh (KEYLENGTH + 2)) }
      pnPath := parentPath
      let pn' ← nodeAt pnPath
      cindex := KeyVector.getIndex pkey pn'
      continue
    let n := pn.child cindex
    if ← branch .ftfNull n.isNone then continue
    let some c := n | invariant "fib_table_flush: unreachable"
    if ← branchCmp .ftfTnode (c.bits != 0) c.bits 0 then
      pnPath := pnPath ++ [cindex]
      cindex := 2 ^ c.bits
      continue
    -- the leaf's aliases
    let nPath := pnPath ++ [cindex]
    let mut slen : Nat := 0
    let mut kept : List FibAlias := []
    for fa in c.aliases do
      _ ← branch .ftfAliasIterate true
      let fi? := (← getTable).infos.get? fa.info
      -- `if (!fi || tb->tb_id != fa->tb_id || (!(fi->fib_flags & RTNH_F_DEAD) && !fib_props[fa->fa_type].error))`
      let mut keep := false
      if ← branch .ftfNoInfo fi?.isNone then keep := true
      else if ← branchCmp .ftfOtherTable (tbId != fa.tbId) tbId fa.tbId then keep := true
      else
        let some fi := fi? | invariant "fib_table_flush: unreachable"
        let dead : Nat := fi.flags &&& RTNH_F_DEAD
        if ← branchCmp .ftfNotDead (dead == 0) dead 0 then
          let errCode : Nat := if fa.type.error == 0 then 0 else 1
          if ← branchCmp .ftfNoError (errCode == 0) errCode 0 then keep := true
      if keep then
        slen := fa.slen
        kept := kept ++ [fa]
        continue
      let some fi := fi? | invariant "fib_table_flush: unreachable"
      -- `if (!flush_all && fib_props[fa->fa_type].error && !(fi->fib_flags & RTNH_F_DEAD))`
      let mut skip := false
      if ← branch .ftfNotFlushAll !flushAll then
        if ← branch .ftfErrorType (fa.type.error != 0) then
          if ← branch .ftfErrorNotDead (fi.flags &&& RTNH_F_DEAD == 0) then skip := true
      if skip then
        slen := fa.slen
        kept := kept ++ [fa]
        continue
      -- notify over the list as it stands (the kept and the not yet
      -- visited aliases), rtmsg (`pfsrc_removed`: never set on these
      -- paths), delete, release
      let current := kept ++ (c.aliases.drop (kept.length + found))
      notifyAliasDelete current kept.length
      if ← branchCmp .ftfPfsrcRemoved false 0 0 then pure ()
      releaseInfo fa.info
      found := found + 1
    _ ← branch .ftfAliasIterate false
    let leaf' := (c.withAliases kept).withSlen slen
    setNode nPath (some leaf')
    if ← branch .ftfEmptied kept.isEmpty then
      let pn ← nodeAt pnPath
      let pn' ← putChildRoot pn c.key none
      setNode pnPath (some pn')
  return found

/-- `fib_sync_down_dev(dev, event, force)` (fib_semantics.c:2004-2068): the
    nexthops on `dev` whose scope is not the exempt one (`RT_SCOPE_NOWHERE`
    without force, none with it) go dead (`NETDEV_DOWN`/`UNREGISTER`) or
    linkdown (`NETDEV_CHANGE`); an info whose nexthops all died is dead.
    Returns the count of such infos. The mirror walks its namespace's
    infos only (the design note, 5(b)). -/
def syncDownDev (dev : Nat) (unregisterOrDown : Bool) (force : Bool) : M Nat := do
  let scope : Int := if force then -1 else RT_SCOPE_NOWHERE
  let mut ret := 0
  for (id, fi) in (← getTable).infos do
    if fi.dev != dev then continue
    let mut dead := 0
    let mut fi' := fi
    if fi.nhFlags &&& RTNH_F_DEAD != 0 then dead := dead + 1
    else if fi.dev == dev && (fi.nhScope : Int) != scope then
      if unregisterOrDown then fi' := { fi' with nhFlags := fi'.nhFlags ||| RTNH_F_DEAD }
      fi' := { fi' with nhFlags := fi'.nhFlags ||| RTNH_F_LINKDOWN }
      dead := dead + 1
    if dead == 1 then
      if unregisterOrDown then fi' := { fi' with flags := fi'.flags ||| RTNH_F_DEAD }
      fi' := { fi' with flags := fi'.flags ||| RTNH_F_LINKDOWN }
      ret := ret + 1
    modifyTable fun tb => { tb with infos := tb.infos.insert id fi' }
  return ret

/-- `fib_flush(net)` (fib_frontend.c:184-197): one `fib_table_flush` per
    table in the hash, MAIN then LOCAL, over the one aliased trie, then
    `rt_cache_flush` if anything went. -/
def fibFlush : M Unit := do
  let a ← tableFlush RT_TABLE_MAIN false
  let b ← tableFlush RT_TABLE_LOCAL false
  if a + b > 0 then rtCacheFlush

/-- `arp_ifdown(dev)` → `neigh_ifdown`: the device's neighbour entries go. -/
def arpIfdown (dev : Nat) : M Unit :=
  modify fun w => { w with neighbours := w.neighbours.filter fun (d, _, _) => d != dev }

/-- `fib_disable_ip(dev, event, force)` (fib_frontend.c:1436-1444). -/
def disableIp (dev : Nat) (force : Bool) : M Unit := do
  if (← syncDownDev dev true force) > 0 then fibFlush else rtCacheFlush
  arpIfdown dev

/-- `fib_magic(cmd, type, dst, dst_len, ifa, rt_priority)` (fib_frontend.c:1083-1121):
    `prefsrc` is the primary's `ifa_local`, `dev` its device. -/
def fibMagic (add : Bool) (type : RouteType) (dst dstLen : Nat) (prefsrc dev : Nat) (priority : Nat) : M Unit := do
  let tbId := if type == .unicast then RT_TABLE_MAIN else RT_TABLE_LOCAL
  let cfg : Config := { dst, dstLen, table := tbId, protocol := RTPROT_KERNEL, type, prefsrc, oif := dev,
                        priority, nlflags := NLM_F_CREATE ||| NLM_F_APPEND,
                        scope := if type != .local then RT_SCOPE_LINK else RT_SCOPE_HOST }
  if add then _ ← tableInsert cfg else _ ← tableDelete cfg

/-- `fib_add_ifaddr(ifa)` (fib_frontend.c:1123-1167) for a primary address
    `addr/prefixlen` on `dev`, with the device's up state. -/
def addIfaddr (dev : Nat) (addr prefixlen : Nat) (devUp : Bool) : M Unit := do
  let mask := if prefixlen == 0 then 0 else (KEY_MAX - (2 ^ (KEYLENGTH - prefixlen) - 1))
  let pfx := addr &&& mask
  fibMagic true .local addr 32 addr dev 0
  if !devUp then return
  -- an explicit broadcast: the fixture sets none (`ifa_broadcast` 0)
  if pfx / 2 ^ 24 != 0 && (pfx != addr || prefixlen < 32) then
    fibMagic true (if dev == LO_IFINDEX then .local else .unicast) pfx prefixlen addr dev 0
    if prefixlen < 31 then
      fibMagic true .broadcast (pfx ||| (KEY_MAX - mask)) 32 addr dev 0

/-- `fib_sync_down_addr(dev, local)` (fib_semantics.c:1908-1927): the infos
    with this prefsrc on the device go dead; the mirror walks its
    namespace's infos (the design note, 5(b)). -/
def syncDownAddr (dev addr : Nat) : M Nat := do
  let mut n := 0
  for (id, fi) in (← getTable).infos do
    if fi.prefsrc == addr && fi.dev == dev && fi.flags &&& RTNH_F_DEAD == 0 then
      modifyInfo id fun o => { o with flags := o.flags ||| RTNH_F_DEAD }
      n := n + 1
  return n

/-- `fib_del_ifaddr(ifa, NULL)` (fib_frontend.c:1197-1345) for a primary
    address with no explicit broadcast (the fixture sets none) that was the
    device's only one, or on a dying device (`in_dev->dead`, which skips the
    scan): `ok` is 0, `gone` is 1. -/
def delIfaddr (dev : Nat) (addr prefixlen : Nat) (devDead : Bool) : M Unit := do
  let mask := if prefixlen == 0 then 0 else (KEY_MAX - (2 ^ (KEYLENGTH - prefixlen) - 1))
  let any := addr &&& mask
  let brd := addr ||| (KEY_MAX - mask)
  let mut subnet := false
  -- :1228-1234: the prefix route of a primary
  if any / 2 ^ 24 != 0 && (any != addr || prefixlen < 32) then
    fibMagic false (if dev == LO_IFINDEX then .local else .unicast) any prefixlen addr dev 0
    subnet := true
  if !devDead then
    -- :1241-1313: the scan over the device's other addresses
    if (← deviceAddrs dev).any (fun (a, _) => a != addr) then
      unsupported "fib_del_ifaddr with another address on the device (address promotion)"
  -- no_promotions (:1314-1345): `ok` is 0
  fibMagic false .broadcast 0 32 addr dev 0   -- `ifa->ifa_broadcast` is 0
  if subnet && prefixlen < 31 then
    fibMagic false .broadcast brd 32 addr dev 0
    fibMagic false .broadcast any 32 addr dev 0
  fibMagic false .local addr 32 addr dev 0
  -- `addr_type = inet_addr_type_dev_table(dev_net(dev), dev, ifa->ifa_local)`
  let addrType ← inetDevAddrType (some dev) addr
  if addrType != .local then
    if (← syncDownAddr dev addr) > 0 then fibFlush

/-- `fib_inetaddr_event` `NETDEV_UP` (fib_frontend.c:1446-1458): an address
    added. -/
def inetaddrUp (dev : Nat) (addr prefixlen : Nat) : M Unit := do
  addIfaddr dev addr prefixlen (← deviceUp dev)
  devAddrGenidBump
  rtCacheFlush

/-- `fib_inetaddr_event` `NETDEV_DOWN` (fib_frontend.c:1459-1471): an address
    deleted; the last one disables IP on the device. -/
def inetaddrDown (dev : Nat) (addr prefixlen : Nat) (last devDead : Bool) : M Unit := do
  delIfaddr dev addr prefixlen devDead
  devAddrGenidBump
  if last then disableIp dev true else rtCacheFlush

/-- `fib_netdev_event` `NETDEV_UP` (fib_frontend.c:1491-1500): every address
    of the device added again. -/
def netdevUp (dev : Nat) : M Unit := do
  for (a, _) in ← deviceAddrs dev do
    addIfaddr dev a (if dev == LO_IFINDEX then 8 else 32) true
  devAddrGenidBump
  rtCacheFlush

/-- `fib_netdev_event` `NETDEV_DOWN` (:1501-1503) and `NETDEV_UNREGISTER`
    (:1487-1490, with `rt_flush_dev`). -/
def netdevDown (dev : Nat) : M Unit := disableIp dev false
def netdevUnregister (dev : Nat) : M Unit := disableIp dev true

/-- `fib_netdev_event` `NETDEV_CHANGEMTU` (:1519-1522) and nexthop.c's
    (3884-3887): `fib_sync_mtu` touches only cached routes; two flushes. -/
def netdevChangeMtu : M Unit := do
  rtCacheFlush
  rtCacheFlush

/-- The guest's `route_into_wg0` requests (guest.c:1212-1294) for IPv4: the
    address (`RTM_NEWADDR` → `inet_rtm_newaddr` → `__inet_insert_ifa` →
    `NETDEV_UP`), the default route (`RTM_NEWROUTE`, table main, scope link,
    type unicast, `oif` wg0, protocol static) and the W4 host routes with
    their MTU. `addrAlready`: the IPv4 address survived a down (`-EEXIST`,
    nothing added). -/
def routeIntoWg0 (addrAlready : Bool) (addr : Nat) (routes : List (Nat × Nat)) : M Unit := do
  if !addrAlready then inetaddrUp WG0_IFINDEX addr 32
  let defaultRoute : Config := { table := RT_TABLE_MAIN, protocol := RTPROT_STATIC, scope := RT_SCOPE_LINK,
                                 type := .unicast, oif := WG0_IFINDEX, nlflags := NLM_F_CREATE ||| NLM_F_EXCL }
  _ ← tableInsert defaultRoute
  for (dst, mtu) in routes do
    let r : Config := { dst, dstLen := 32, table := RT_TABLE_MAIN, protocol := RTPROT_STATIC, scope := RT_SCOPE_LINK,
                        type := .unicast, oif := WG0_IFINDEX, mtu, nlflags := NLM_F_CREATE ||| NLM_F_EXCL }
    _ ← tableInsert r

/-- The guest's `wg_delroute` (`delroute_wg0`, guest.c:707-721): `RTM_DELROUTE`
    of the default route via wg0 (table main, protocol static, scope link,
    type unicast, `oif` wg0, no destination). -/
def delrouteWg0 : M Int :=
  tableDelete { table := RT_TABLE_MAIN, protocol := RTPROT_STATIC, scope := RT_SCOPE_LINK, type := .unicast,
                oif := WG0_IFINDEX }

/-- The boot of the fixture namespace: `lo` up (devinet.c:1601-1613 adds
    `127.0.0.1/8` through `inet_insert_ifa` → `NETDEV_UP`). Run before the
    first operation; its decisions fall outside every window. -/
def bootTables : M Unit := do
  inetaddrUp LO_IFINDEX LOOPBACK4 8

/-! ## The shape oracle (`/proc/net/fib_trie`, fib_trie.c:2780-2813) -/

def dotted (key : Nat) : String :=
  s!"{key / 2 ^ 24 % 256}.{key / 2 ^ 16 % 256}.{key / 2 ^ 8 % 256}.{key % 256}"

def scopeName : Nat → String
  | 0 => "universe" | 200 => "site" | 253 => "link" | 254 => "host" | 255 => "nowhere"
  | n => s!"scope={n}"

def typeName : RouteType → String
  | .unspec => "UNSPEC" | .unicast => "UNICAST" | .local => "LOCAL" | .broadcast => "BROADCAST"
  | .anycast => "ANYCAST" | .multicast => "MULTICAST" | .blackhole => "BLACKHOLE"
  | .unreachable => "UNREACHABLE" | .prohibit => "PROHIBIT" | .throw => "THROW"

/-- The printed shape as JSON: a tnode is `[prefix, plen, bits, full, empty,
    children]`, a leaf `[key, aliases]` with each alias `[plen, scope,
    type, tos]`; the children in index order, empty slots omitted, as the
    proc walk prints them. -/
def shapeOf (k : Kernel) : Nat → KeyVector → Lean.Json
  | _, .leaf key _ aliases =>
    Lean.Json.arr #[Lean.toJson (dotted key),
      Lean.Json.arr (aliases.map fun fa =>
        let scope := (k.fib4.infos.get? fa.info).map (·.scope) |>.getD 0
        Lean.Json.arr #[Lean.toJson (KEYLENGTH - fa.slen), Lean.toJson (scopeName scope),
                        Lean.toJson (typeName fa.type), Lean.toJson fa.dscp]).toArray]
  | 0, .tnode key pos bits _ _ e f _ =>
    Lean.Json.arr #[Lean.toJson (dotted key), Lean.toJson (KEYLENGTH - pos - bits), Lean.toJson bits,
                    Lean.toJson f, Lean.toJson e, Lean.Json.arr #[]]
  | fuel + 1, .tnode key pos bits _ children e f _ =>
    Lean.Json.arr #[Lean.toJson (dotted key), Lean.toJson (KEYLENGTH - pos - bits), Lean.toJson bits,
                    Lean.toJson f, Lean.toJson e,
                    Lean.Json.arr (children.filterMap (·.map (shapeOf k fuel)))]

/-- The namespace's trie as the proc file shows it (`Main:`), `null` for an
    empty trie. -/
def shape (k : Kernel) : Lean.Json :=
  match k.fib4.trie.root with
  | some n => shapeOf k (KEYLENGTH + 2) n
  | none => Lean.Json.null

end Leanux.Net.Fib
