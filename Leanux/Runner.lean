import Leanux.Syscalls
import Lean.Data.Json

namespace Leanux.Runner
open Lean Leanux

inductive FDArg where
  | literal (value : Int)
  | ref (index : Nat)
  /-- `{"pipe": i, "end": e}`: end `e` (0 = `fd[0]`, the read end; 1 =
      `fd[1]`, the write end) of the earlier `pipe2` at index `i`. -/
  | pipe (index : Nat) (endIdx : Nat)
  deriving Repr

/-- The byte-count bound for `read` and `write` (P design section 6, Q5): 17
    pages, so one write can overfill the default 16-slot ring. -/
def MAX_IO : Nat := 69632
/-- Bytes of a read shown in the clear (`bytes`); the `digest` covers all. -/
def READ_HEAD : Nat := 64
/-- The fixture pause before an operation's coverage window, in ms. -/
def PAUSE_MS_MAX : Nat := 20

inductive Operation where
  | eventfd2 (init flags : UInt32)
  | dup (fd : FDArg)
  | dup3 (fd newfd : FDArg) (flags : UInt32)
  | close (fd : FDArg)
  | read (fd : FDArg) (count : Nat)
  | write (fd : FDArg) (count : Nat) (value : UInt64)
  | fcntl (fd : FDArg) (cmd : FcntlCmd) (arg : UInt32)
  /-- `pipe2(fildes, flags)` (P). -/
  | pipe2 (flags : UInt32)
  /-- epoll (contracts/trace-v1.md, Epoll): a set (a producer); an item
      operation on set `epfd` for target `fd` (`cmd` and `events` u32, `data`
      a u64); a wait for `maxevents` events with `timeout`. -/
  | epollCreate1 (flags : UInt32)
  | epollCtl (epfd : FDArg) (cmd : UInt32) (fd : FDArg) (events : UInt32) (data : UInt64)
  | epollWait (epfd : FDArg) (maxevents timeout : Int)
  | wgSet (attrs : WG.DeviceAttrs)
  /-- `wg_get` with its device selector (W1). -/
  | wgGet (device : WG.DeviceRef)
  /-- W2: the stepped dump on fd 8 (`wg_get_start` with the selector; one
      `wg_get_recv` per chunk). -/
  | wgGetStart (device : WG.DeviceRef)
  | wgGetRecv
  | wgUp
  /-- `tos` (W5) rides in `opts` (`Env.XmitOpts.tos`): the sender's TOS /
      traffic class for this send, the inner TOS of the transmitted packet. -/
  | wgXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
  /-- W4 (docs/2026-10-06-w4-w7-transmit-bulk.md section 6): `SIOCSIFMTU` on wg0. -/
  | wgSetMtu (mtu : Nat)
  | wgObserve
  /-- `tos` (W5): the outer DS field of the injection; `ll`: sent from the
      link-local address on lo (`from: "ll"`, family 6); `dest` (W9, `to`):
      0 the loopback address, 1 wg0's own address, 2 the loopback alias. -/
  | wgInject (family port : Nat) (message : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
  /-- W9: the fixture-table operations, per family. -/
  | wgDeladdr (family : Nat)
  | wgDelroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat)
  /-- Lane C: `wg_addroute` and `wg_addaddr` (the design note, 10). -/
  | wgAddroute (dst plen oif typeCode metric mtu nlflags : Nat)
  | wgAddaddr (addr plen : Nat)
  /-- E-B: an io_uring flood of `count` invalid-MAC1 initiations to wg0's port,
      with `messages` valid-MAC1 initiations submitted first (processed under
      load via the queue depth, their cookie replies checked byte-exact);
      docs/2026-10-05-e-dos.md §8. -/
  | wgFlood (count port family : Nat) (messages : List (List UInt8))
  /-- W7: an io_uring batch of injects and transmits (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5). -/
  | wgBatch (items : List Env.BatchItem) (waitMs : Nat)
  /-- D3: the virtual time advance (harness/trace.py `wg_advance`). -/
  | wgAdvance (ticks : Nat)
  /-- L (docs/2026-10-05-l-lifecycle.md): wg0's lifecycle. -/
  | wgCreate
  | wgDown
  | wgDelete
  | wgNetnsClose
  /-- seccomp (docs/2026-10-12-seccomp-design.md 6.1): `seccomp_install` 30,
      `seccomp_probe` 31, `seccomp_prctl` 32 (`args` is `arg2..arg5`),
      `seccomp_capdrop` 33, `seccomp_query` 34. -/
  | seccompInstall (via : Seccomp.InstallVia) (flags : UInt32) (filter : Option ClassicProg)
      (len : Option Nat) (bad : Seccomp.BadPtr) (mode : Nat)
  | seccompProbe (nr : Int) (args : Array UInt64) (where_ : Seccomp.ProbeWhere) (strict : Option Seccomp.StrictVia)
  | seccompPrctl (cmd : Seccomp.PrctlCmd) (args : Array UInt64)
  | seccompCapdrop
  | seccompQuery (cmd : Seccomp.QueryCmd) (action flags : UInt32)
  deriving Repr

/-- The operations a `{"ref": i}` may name. -/
def Operation.isProducer : Operation → Bool
  | .eventfd2 .. | .dup .. | .dup3 .. | .epollCreate1 .. => true
  | _ => false

/-- The operations a `{"pipe": i, "end": e}` may name. -/
def Operation.isPipe : Operation → Bool
  | .pipe2 _ => true
  | _ => false

/-- The descriptor arguments of an operation, for the parser's domain rule
    (`reservedFds`). Every constructor is listed, so a new one with a
    descriptor cannot slip past the rule unnoticed. -/
def Operation.descriptors : Operation → List FDArg
  | .dup fd | .close fd | .read fd _ | .write fd _ _ | .fcntl fd _ _ | .epollWait fd _ _ => [fd]
  | .dup3 fd newfd _ => [fd, newfd]
  | .epollCtl epfd _ fd _ _ => [epfd, fd]
  | .eventfd2 .. | .pipe2 _ | .epollCreate1 _
  | .wgSet _ | .wgGet _ | .wgGetStart _ | .wgGetRecv | .wgUp | .wgXmit .. | .wgSetMtu _ | .wgObserve
  | .wgInject .. | .wgDeladdr _ | .wgDelroute .. | .wgAddroute .. | .wgAddaddr .. | .wgFlood ..
  | .wgBatch .. | .wgAdvance _ | .wgCreate | .wgDown | .wgDelete | .wgNetnsClose
  | .seccompInstall .. | .seccompProbe .. | .seccompPrctl .. | .seccompCapdrop | .seccompQuery .. => []

/-- The fixture's reserved descriptors: 0-2 the console, 3 the KCOV fd, 4-7
    the fixture's sockets or fillers; 8 the stepped dump's socket (W2) or the
    seccomp child's KCOV fd; 8 and 9 the foreign-creator fixture's injector
    and namespace pin (W8). A trace names none of them: a literal below the
    count is outside the domain (`parseTrace`, with `harness/trace.py`'s
    matching rule), as a user operation on the harness's own apparatus. -/
def reservedFds (foreign stepped seccompChild : Bool) : Nat :=
  if foreign then 10 else if stepped || seccompChild then 9 else 8

structure Trace where
  id : String
  ops : Array Operation
  /-- `RLIMIT_NOFILE`, set by the fixture before the first operation. -/
  rlimit : Nat := 32
  /-- The hidden-input records Linux made for each operation (the check adds
      them after the Linux run; docs/2026-10-03-hidden-inputs-design.md). -/
  hidden : Option (Array (List HiddenRecord)) := none
  /-- A steering schedule (choice-stream strategy, step 2): the placeholders
      follow it; Linux's records carry the steered values. -/
  steer : List (String × Option (List UInt8)) := []
  /-- D3: whether `hidden` includes the kind-303 arm records (the check sets
      it from `harness/linux.py` `ARM_RECORDS`, the wire's `A` line). -/
  armRecords : Bool := false
  /-- W9: `"dst_cache_records": false` marks a capture made before the
      kind-306 records (the replay tests only). -/
  dstCacheRecords : Bool := true
  /-- The check's choice for each NAPI poll placement the records leave open
      (`World.napiBeforePut`). -/
  napiBeforePut : List Bool := []
  /-- `"net_fixture": "bare"` (L): the network fixture without wg0. -/
  bare : Bool := false
  /-- W4: `"net_fixture": {"routes": [...]}`, the routes the fixture adds into
      wg0 at every `wg_up` (family, destination, MTU): `World.routes`. -/
  routes : List (Nat × Nat × Nat) := []
  /-- `"net_fixture": "foreign-creator"` (W8): wg0 created from a second
      namespace, held by the fixture's descriptors 4, 5, 8 and 9. -/
  foreign : Bool := false
  /-- The allocation sites the run armed (the check adds them with the
      records): their outcomes are consumed from the records. -/
  allocArmed : List String := []
  /-- Each operation's `pause_ms` (0 when absent): a fixture sleep before the
      operation's coverage window, ignored by the mirror (only the clock
      advances). -/
  pauses : Array Nat := #[]
  /-- `"seccomp_child": true` (seccomp design 6.2 rule 2): the second KCOV
      descriptor, 8, opened and mapped by the trace process at setup for the
      sandboxed children; exclusive with a network fixture (design 5). -/
  seccompChild : Bool := false
  /-- `"seccomp_prefill": N` (design 5): the guest installed `N` copies of the
      prefill program under no-new-privs before the window; the initial task
      state carries the chain (`Env.seccompPrefill`). -/
  seccompPrefill : Nat := 0
  deriving Repr

/-- The network fixture runs for traces with a WireGuard operation
    (harness/trace.py `uses_wireguard`). -/

def Trace.net (t : Trace) : Bool :=
  t.ops.any fun
    | .wgSet _ | .wgGet _ | .wgUp | .wgXmit .. | .wgObserve | .wgInject .. | .wgAdvance _
    | .wgFlood _ _ _ _ | .wgCreate | .wgDown | .wgDelete | .wgSetMtu _ | .wgBatch _ _
    | .wgDeladdr _ | .wgDelroute .. | .wgNetnsClose | .wgGetStart _ | .wgGetRecv
    | .wgAddroute .. | .wgAddaddr .. => true
    | _ => false

/-- W2: a trace with a stepped dump operation gets the dump socket at fd 8. -/
def Trace.stepped (t : Trace) : Bool :=
  t.ops.any fun | .wgGetStart _ | .wgGetRecv => true | _ => false

private def fields (j : Json) (expected : List String) : Except String Unit := do
  let obj ← j.getObj?
  if obj.size != expected.length || !obj.all (fun key _ => expected.contains key) then
    throw s!"expected exactly fields {expected}"

private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name

private def natField (j : Json) (name : String) (bound : Nat) : Except String Nat := do
  let n ← (← field j name).getNat?
  if n > bound then throw s!"{name} out of range"
  return n

private def u32Field (j : Json) (name : String) : Except String UInt32 :=
  UInt32.ofNat <$> natField j name 4294967295

private def parseFD (j : Json) (prior : Array Operation) : Except String FDArg := do
  let obj ← j.getObj?
  if let some v := obj.get? "pipe" then
    fields j ["pipe", "end"]
    let n ← v.getNat?
    let e ← natField j "end" 1
    match prior[n]? with
    | some op =>
      if op.isPipe then return .pipe n e
      else throw "pipe reference must name a pipe2"
    | none => throw "pipe reference must name an earlier operation"
  if obj.size != 1 then throw "descriptor argument needs one field"
  if let some v := obj.get? "literal" then
    let n ← v.getInt?
    if n < -2147483648 || n > 2147483647 || (0 ≤ n && n < 8) then
      throw "descriptor literal outside domain"
    return .literal n
  else if let some v := obj.get? "ref" then
    let n ← v.getNat?
    match prior[n]? with
    | some op =>
      if op.isProducer then return .ref n
      else throw "reference must name a producer"
    | none => throw "reference must name an earlier operation"
  else throw "unknown descriptor field"

private def parseU64Field (j : Json) (name : String) : Except String UInt64 := do
  let s ← (← field j name).getStr?
  let some n := s.toNat? | throw s!"{name} must be decimal"
  if toString n != s || n > 18446744073709551615 then
    throw s!"{name} must be canonical UInt64 decimal"
  return UInt64.ofNat n

private def parseValue (j : Json) : Except String UInt64 := parseU64Field j "value"

/-- A signed 32-bit integer field (the kernel's `int`). -/
private def int32Field (j : Json) (name : String) : Except String Int := do
  let n ← (← field j name).getInt?
  if n < -2147483648 || n > 2147483647 then throw s!"{name} out of range"
  return n


/-! ## WireGuard configurations

The trace's structured configuration (harness/wg.py `validate_config`), read
as the attributes `encode_set` sends. Keys and addresses are lowercase hex. -/

private def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none


/-- Exactly `digits` lowercase hex digits, as bytes. -/
private def hexBytes (j : Json) (digits : Nat) (what : String) : Except String (List UInt8) := do
  let s ← j.getStr?
  let cs := s.toList
  if cs.length != digits then throw s!"{what}: expected {digits} lowercase hex digits"
  let some vs := cs.mapM hexValue | throw s!"{what}: expected {digits} lowercase hex digits"
  let rec pairs : List Nat → List UInt8
    | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: pairs rest
    | _ => []
  return pairs vs

private def bigEndian (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

private def optNat (j : Json) (name : String) (bound : Nat) : Except String Nat :=
  match j.getObjVal? name with
  | .error _ => pure 0
  | .ok _ => natField j name bound

/-- Lane C: a route's device, `wg0` or `lo`, 0 when absent. -/
private def routeOif (j : Json) : Except String Nat :=
  match j.getObjVal? "oif" with
  | .error _ => pure 0
  | .ok o => do
    match ← o.getStr? with
    | "lo" => pure LO_IFINDEX
    | "wg0" => pure WG0_IFINDEX
    | _ => throw "oif: expected wg0 or lo"

/-- Lane C: a route's type as its `RTN_` code; required for an add, 0 (any)
    when absent from a delete. -/
private def routeType (j : Json) (required : Bool) : Except String Nat :=
  match j.getObjVal? "type" with
  | .error _ => if required then throw "type: expected unicast, unreachable, blackhole or prohibit" else pure 0
  | .ok t => do
    match ← t.getStr? with
    | "unicast" => pure 1
    | "unreachable" => pure 7
    | "blackhole" => pure 6
    | "prohibit" => pure 8
    | _ => throw "type: expected unicast, unreachable, blackhole or prohibit"

private def subsetFields (j : Json) (allowed : List String) (what : String) : Except String Unit := do
  let obj ← j.getObj?
  if !obj.all (fun key _ => allowed.contains key) then throw s!"{what}: fields must be a subset of {allowed}"

private def optField (j : Json) (name : String) : Option Json := (j.getObjVal? name).toOption

/-- W5: the optional `tos` of a `wg_inject` or `wg_xmit` (0-255; 0 absent). -/
private def senderTos (j : Json) : Except String Nat :=
  match j.getObjVal? "tos" with
  | .ok v => do
    let n ← v.getNat?
    if n > 255 then throw "tos: expected 0-255"
    pure n
  | .error _ => pure 0

private def boolField (j : Json) (name : String) : Except String Bool := do
  match optField j name with
  | none => return false
  | some v => v.getBool?

private def address (j : Json) (withPort : Bool) (what : String) : Except String (Nat × Nat × Nat × Nat) := do
  fields j (if withPort then ["family", "addr", "port"] else ["family", "addr", "cidr"])
  let family ← (← field j "family").getNat?
  if family != 4 && family != 6 then throw s!"{what}.family: expected 4 or 6"
  let len := if family == 4 then 4 else 16
  let addr := bigEndian (← hexBytes (← field j "addr") (2 * len) s!"{what}.addr")
  let last ← if withPort then natField j "port" 65535 else natField j "cidr" 255
  return (if family == 4 then WG.AF_INET else WG.AF_INET6, addr, len, last)

/-- W1 (harness/wg.py `_endpoint`): `family`, `addr` (4 or 16 bytes, any
    16 for IPv6), `port`; optionally `flowinfo` and `scope_id` (IPv6 only),
    `af` (the `sa_family` bytes, overriding the family's) and `len` (16..128,
    the attribute's length; the canonical sockaddr zero-padded or truncated). -/
private def parseEndpoint (j : Json) (what : String) : Except String WG.EndpointAttr := do
  subsetFields j ["family", "addr", "port", "flowinfo", "scope_id", "af", "len"] what
  let family ← (← field j "family").getNat?
  if family != 4 && family != 6 then throw s!"{what}.family: expected 4 or 6"
  let len := if family == 4 then 4 else 16
  let addr := bigEndian (← hexBytes (← field j "addr") (2 * len) s!"{what}.addr")
  let port ← natField j "port" 65535
  if family != 6 && ((optField j "flowinfo").isSome || (optField j "scope_id").isSome) then
    throw s!"{what}: flowinfo and scope_id are IPv6 only"
  let flowinfo ← if (optField j "flowinfo").isSome then natField j "flowinfo" 4294967295 else pure 0
  let scope ← if (optField j "scope_id").isSome then natField j "scope_id" 4294967295 else pure 0
  let af ← if (optField j "af").isSome then natField j "af" 65535
    else pure (if family == 4 then WG.AF_INET else WG.AF_INET6)
  -- sizeof(struct sockaddr_in) or sizeof(struct sockaddr_in6) unless `len` says otherwise
  let attrLen ← if (optField j "len").isSome then natField j "len" 128 else pure (if family == 4 then 16 else 28)
  if attrLen < 16 then throw s!"{what}.len: below 16 the policy rejects (P8)"
  -- netlink audit F1 (docs/2026-10-13-audit-netlink.md): `set_peer`
  -- (netlink.c:441-446) reads the bytes by `len` and `sa_family` alone; one
  -- family's bytes under the other layout are an endpoint these parsed
  -- fields cannot express, so the trace is refused (the validator agrees)
  if family == 4 && af == WG.AF_INET6 && attrLen == 28 then
    throw s!"{what}: af 10 with len 28 presents family-4 bytes under the sockaddr_in6 layout: not modelled, refused"
  if family == 6 && af == WG.AF_INET && attrLen == 16 then
    throw s!"{what}: af 2 with len 16 presents family-6 bytes under the sockaddr_in layout: not modelled, refused"
  pure { len := attrLen, family := af, addr, port, flowinfo, scope }

/-- W1 (harness/wg.py `_allowed_ip`): any subset of `family`, `addr` (4..20
    bytes) and `cidr`; `af` overrides the family value; `malformed:
    "not_nested"` is the entry without `NLA_F_NESTED`. -/
private def parseAllowedIp (j : Json) (what : String) : Except String WG.AllowedIpEntry := do
  subsetFields j ["family", "addr", "cidr", "af", "malformed"] what
  if let some m := optField j "malformed" then
    if (← m.getStr?) != "not_nested" then throw s!"{what}.malformed: expected \"not_nested\""
    return .malformed
  let family ← (optField j "family").mapM fun v => do
    let f ← v.getNat?
    if f != 4 && f != 6 then throw s!"{what}.family: expected 4 or 6"
    pure (if f == 4 then WG.AF_INET else WG.AF_INET6)
  let family ← if (optField j "af").isSome then some <$> natField j "af" 65535 else pure family
  let addrBytes ← (optField j "addr").mapM fun v => do
    let s ← v.getStr?
    if s.length < 8 || s.length > 40 || s.length % 2 != 0 then throw s!"{what}.addr: expected 4-20 bytes of hex"
    hexBytes v s.length s!"{what}.addr"
  let cidr ← (optField j "cidr").mapM fun _ => natField j "cidr" 255
  pure (.attrs { family, addr := addrBytes.map bigEndian, addrLen := (addrBytes.map (·.length)).getD 0, cidr })

private def parsePeer (j : Json) (i : Nat) : Except String WG.PeerEntry := do
  let what := s!"config.peers[{i}]"
  subsetFields j ["public_key", "remove", "update_only", "replace_allowed_ips", "flags", "preshared_key",
    "endpoint", "keepalive", "allowed_ips", "protocol_version", "malformed"] what
  if let some m := optField j "malformed" then
    if (← m.getStr?) != "not_nested" then throw s!"{what}.malformed: expected \"not_nested\""
    return .malformed
  let publicKey ← (optField j "public_key").mapM (hexBytes · 64 s!"{what}.public_key")
  let booleans := ["remove", "update_only", "replace_allowed_ips"].any fun f => (optField j f).isSome
  let flags ← if (optField j "flags").isSome then do
      if booleans then throw s!"{what}.flags: exclusive with remove, update_only, replace_allowed_ips"
      some <$> u32Field j "flags"
    else do
      let f := (if ← boolField j "remove" then WG.WGPEER_F_REMOVE_ME else 0) |||
        (if ← boolField j "update_only" then WG.WGPEER_F_UPDATE_ONLY else 0) |||
        (if ← boolField j "replace_allowed_ips" then WG.WGPEER_F_REPLACE_ALLOWEDIPS else 0)
      pure (if f != 0 then some f else none)
  let protocolVersion ← (optField j "protocol_version").mapM fun _ => natField j "protocol_version" 4294967295
  let presharedKey ← (optField j "preshared_key").mapM (hexBytes · 64 s!"{what}.preshared_key")
  let endpoint ← (optField j "endpoint").mapM (parseEndpoint · s!"{what}.endpoint")
  let keepalive ← (optField j "keepalive").mapM fun _ => natField j "keepalive" 65535
  let allowedIps ← (optField j "allowed_ips").mapM fun a => do
    let ips ← a.getArr?
    if ips.size > 32 then throw s!"{what}.allowed_ips: expected at most 32 entries"
    ips.toList.mapIdxM fun k ip => parseAllowedIp ip s!"{what}.allowed_ips[{k}]"
  return .attrs { publicKey, presharedKey, flags, protocolVersion, endpoint, keepalive, allowedIps }

/-- W1: the device selector (harness/wg.py `validate_device`): `{"ifname":
    s}`, `{"ifindex": n}`, both or `{}`; absent means wg0 by name. -/
private def parseDevice (j : Json) : Except String WG.DeviceRef := do
  match optField j "device" with
  | none => pure {}
  | some d =>
    subsetFields d ["ifname", "ifindex"] "device"
    let ifname ← (optField d "ifname").mapM fun v => do
      let s ← v.getStr?
      if s.isEmpty || s.length > 15 then throw "device.ifname: expected 1-15 characters"
      pure s
    let ifindex ← (optField d "ifindex").mapM fun _ => natField d "ifindex" 4294967295
    pure { ifname, ifindex }

private def parseConfig (j : Json) : Except String WG.DeviceAttrs := do
  subsetFields j ["private_key", "listen_port", "fwmark", "replace_peers", "flags", "peers"] "config"
  let privateKey ← (optField j "private_key").mapM (hexBytes · 64 "config.private_key")
  let listenPort ← (optField j "listen_port").mapM fun _ => natField j "listen_port" 65535
  let fwmark ← (optField j "fwmark").mapM fun _ => natField j "fwmark" 4294967295
  let replace ← boolField j "replace_peers"
  let flags ← if (optField j "flags").isSome then do
      if (optField j "replace_peers").isSome then throw "config.flags: exclusive with replace_peers"
      some <$> u32Field j "flags"
    else pure (if replace then some WG.WGDEVICE_F_REPLACE_PEERS else none)
  let peers ← (optField j "peers").mapM fun p => do
    let ps ← p.getArr?
    if ps.size > 16 then throw "config.peers: expected at most 16 peers"
    ps.toList.mapIdxM fun i peer => parsePeer peer i
  return { flags, privateKey, listenPort, fwmark, peers }

/-- A `wg_xmit` packet object (W4's options included), for `wg_xmit` and
    a `wg_batch` xmit item. -/
private def parsePacket (p : Json) : Except String (Nat × Nat × List UInt8 × Env.XmitOpts) := do
  -- W4: `gso_size` (UDP_SEGMENT) and `pmtudisc` ("do", the sender's default,
  -- or "probe") are optional; a GSO payload may reach 128 segments
  let hasGso := (p.getObjVal? "gso_size").isOk
  let hasPmtu := (p.getObjVal? "pmtudisc").isOk
  let hasPayload := (p.getObjVal? "payload").isOk
  fields p (["family", "dst"] ++ (if hasPayload then ["payload"] else [])
    ++ (if hasGso then ["gso_size"] else []) ++ (if hasPmtu then ["pmtudisc"] else []))
  let gsoSize ← if hasGso then do
      let g ← (← field p "gso_size").getNat?
      if g == 0 || g > 1392 then throw "packet.gso_size: expected 1-1392"
      pure (some g)
    else pure none
  let probe ← if hasPmtu then do
      match ← (← field p "pmtudisc").getStr? with
      | "do" => pure false
      | "probe" => pure true
      | _ => throw "packet.pmtudisc: expected \"do\" or \"probe\""
    else pure false
  let maxPayload := if hasGso then 128 * 1392 else 1392
  -- the UDP payload (D2); without one, the fixture's historic 4 bytes "leux"
  let payload ← match p.getObjVal? "payload" with
    | .ok v => do
      let s ← v.getStr?
      if s.length == 0 || s.length % 2 != 0 || s.length > 2 * maxPayload then
        throw s!"packet.payload: expected 1-{maxPayload} bytes of lowercase hex"
      hexBytes v s.length "packet.payload"
    | .error _ => do
      if hasGso then throw "packet.gso_size: only with a payload"
      pure "leux".toUTF8.toList
  let family ← (← field p "family").getNat?
  if family != 4 && family != 6 then throw "packet.family: expected 4 or 6"
  let bytes ← hexBytes (← field p "dst") (if family == 4 then 8 else 32) "packet.dst"
  let addr := bigEndian bytes
  -- harness/wg.py validate_packet: destinations the sender's IP layer
  -- handles before routing never reach wg0
  let first := addr / 2 ^ 24
  let bad4 := family == 4 && (first == 0 || first == 127 || addr == 0xffffffff || addr == 0x0afffe01)
  let bad6 := family == 6 && (addr == 0 || addr == 1 || addr == 0xfd00ffff000000000000000000000001
                               || addr == 0xfe8000000000000000000000ffff0001   -- the fixture's link-local address on lo (W5)
                               || addr / 2 ^ 32 == 0xffff)
  if bad4 || bad6 then throw "packet.dst: an address the sender does not route into wg0"
  -- a gso_size on IPv6 is beyond the WireGuard boundary: the mirror's
  -- `Env.xmitPackets` answers `unsupported` (the boundary control wc_gso_ipv6)
  return (family, addr, payload, { gsoSize, probe, routeMtu := none })

/-- A classic program as the trace lists it: `[code, jt, jf, k]` per instruction. -/
private def parseClassicProg (j : Json) : Except String ClassicProg := do
  let rows ← j.getArr?
  rows.mapM fun r => do
    let xs ← r.getArr?
    if xs.size != 4 then throw "seccomp_install.filter: expected [code, jt, jf, k] rows"
    let code ← xs[0]!.getNat?
    let jt ← xs[1]!.getNat?
    let jf ← xs[2]!.getNat?
    let k ← xs[3]!.getNat?
    if code > 65535 || jt > 255 || jf > 255 || k > 4294967295 then throw "seccomp_install.filter: a field is out of range"
    pure { code := UInt16.ofNat code, jt := UInt8.ofNat jt, jf := UInt8.ofNat jf, k := UInt32.ofNat k }

/-- `flags` of a `seccomp_install` (design 6.1): absent (0), a number, or a
    list of names and raw bits, OR'ed. -/
private def parseSeccompFlags (j : Json) : Except String UInt32 := do
  match optField j "flags" with
  | none => pure 0
  | some v =>
    match v.getNat? with
    | .ok n => if n > 4294967295 then throw "seccomp_install.flags: out of range" else pure (UInt32.ofNat n)
    | .error _ =>
      let entries ← v.getArr?
      entries.foldlM (init := (0 : UInt32)) fun acc e => do
        match e.getNat? with
        | .ok n => if n > 4294967295 then throw "seccomp_install.flags: out of range" else pure (acc ||| UInt32.ofNat n)
        | .error _ =>
          let bit : UInt32 ← match ← e.getStr? with
            | "tsync" => pure 1
            | "log" => pure 2
            | "spec_allow" => pure 4
            | "new_listener" => pure 8
            | "tsync_esrch" => pure 16
            | "wait_killable_recv" => pure 32
            | other => throw s!"seccomp_install.flags: unknown flag {other}"
          pure (acc ||| bit)

private def parseOperation (j : Json) (prior : Array Operation) : Except String Operation := do
  let op ← (← field j "op").getStr?
  match op with
  | "eventfd2" =>
    fields j ["op", "init", "flags"]
    let init ← u32Field j "init"
    let flags ← u32Field j "flags"
    return .eventfd2 init flags
  | "dup" =>
    fields j ["op", "fd"]
    return .dup (← parseFD (← field j "fd") prior)
  | "dup3" =>
    fields j ["op", "fd", "newfd", "flags"]
    return .dup3 (← parseFD (← field j "fd") prior)
      (← parseFD (← field j "newfd") prior) (← u32Field j "flags")
  | "close" =>
    fields j ["op", "fd"]
    return .close (← parseFD (← field j "fd") prior)
  | "read" =>
    fields j ["op", "fd", "count"]
    return .read (← parseFD (← field j "fd") prior) (← natField j "count" MAX_IO)
  | "write" =>
    fields j ["op", "fd", "count", "value"]
    return .write (← parseFD (← field j "fd") prior) (← natField j "count" MAX_IO)
      (← parseValue j)
  | "pipe2" =>
    fields j ["op", "flags"]
    return .pipe2 (← u32Field j "flags")
  | "epoll_create1" =>
    fields j ["op", "flags"]
    return .epollCreate1 (← u32Field j "flags")
  | "epoll_ctl" =>
    fields j ["op", "epfd", "cmd", "fd", "events", "data"]
    return .epollCtl (← parseFD (← field j "epfd") prior) (← u32Field j "cmd")
      (← parseFD (← field j "fd") prior) (← u32Field j "events") (← parseU64Field j "data")
  | "epoll_wait" =>
    -- the kernel's `int maxevents` and `int timeout`; tier 1's bounds
    -- (1-16, timeout 0) are the validator's, the mirror follows the C
    fields j ["op", "epfd", "maxevents", "timeout"]
    return .epollWait (← parseFD (← field j "epfd") prior) (← int32Field j "maxevents") (← int32Field j "timeout")
  | "fcntl" =>
    fields j ["op", "fd", "cmd", "arg"]
    let fd ← parseFD (← field j "fd") prior
    let cmd ← (← field j "cmd").getStr?
    let arg ← u32Field j "arg"
    match cmd with
    | "F_GETFD" => return .fcntl fd FcntlCmd.getFD arg
    | "F_SETFD" => return .fcntl fd FcntlCmd.setFD arg
    | "F_GETFL" => return .fcntl fd FcntlCmd.getFL arg
    | "F_SETFL" => return .fcntl fd FcntlCmd.setFL arg
    | "F_SETPIPE_SZ" => return .fcntl fd FcntlCmd.setPipeSz arg
    | "F_GETPIPE_SZ" => return .fcntl fd FcntlCmd.getPipeSz arg
    | _ => throw "unsupported fcntl command"
  | "seccomp_install" =>
    subsetFields j ["op", "via", "flags", "filter", "len", "bad", "mode"] "seccomp_install"
    let via ← match ← (← field j "via").getStr? with
      | "seccomp" => pure Seccomp.InstallVia.seccomp
      | "prctl" => pure Seccomp.InstallVia.prctl
      | _ => throw "seccomp_install.via: expected \"seccomp\" or \"prctl\""
    let flags ← parseSeccompFlags j
    let filter ← match optField j "filter" with
      | none | some .null => pure none
      | some f => some <$> parseClassicProg f
    let len ← if (optField j "len").isSome then some <$> natField j "len" 65535 else pure none
    let bad ← match optField j "bad" with
      | none => pure Seccomp.BadPtr.none
      | some b => match ← b.getStr? with
        | "fprog" => pure Seccomp.BadPtr.fprog
        | "insns" => pure Seccomp.BadPtr.insns
        | _ => throw "seccomp_install.bad: expected \"fprog\" or \"insns\""
    -- `mode` (contract): prctl_set_seccomp's mode argument, prctl only, default 2
    let mode ← if (optField j "mode").isSome then natField j "mode" 255 else pure 2
    if (optField j "mode").isSome && via != .prctl then throw "seccomp_install.mode: prctl only"
    return .seccompInstall via flags filter len bad mode
  | "seccomp_probe" =>
    subsetFields j ["op", "nr", "args", "where", "strict"] "seccomp_probe"
    let nr ← (← field j "nr").getInt?
    if nr < -2147483648 || nr > 2147483647 then throw "seccomp_probe.nr: expected an int"
    let args ← match optField j "args" with
      | none => pure Seccomp.zeroArgs
      | some a => do
        let xs ← (← a.getArr?).toList.mapM fun v => do
          let n ← v.getNat?
          if n > 18446744073709551615 then throw "seccomp_probe.args: expected u64 entries"
          pure (UInt64.ofNat n)
        if xs.length > 6 then throw "seccomp_probe.args: at most six"
        pure ((xs ++ List.replicate (6 - xs.length) 0).toArray)
    let where_ ← match ← (← field j "where").getStr? with
      | "self" => pure Seccomp.ProbeWhere.self
      | "child" => pure Seccomp.ProbeWhere.child
      | _ => throw "seccomp_probe.where: expected \"self\" or \"child\""
    let strict ← match optField j "strict" with
      | none | some .null => pure none
      | some v => match ← v.getStr? with
        | "seccomp" => pure (some Seccomp.StrictVia.seccomp)
        | "prctl" => pure (some Seccomp.StrictVia.prctl)
        | _ => throw "seccomp_probe.strict: expected null, \"seccomp\" or \"prctl\""
    if strict.isSome && where_ != .child then throw "seccomp_probe.strict: child only"
    return .seccompProbe nr args where_ strict
  | "seccomp_prctl" =>
    subsetFields j ["op", "cmd", "arg2", "arg3", "arg4", "arg5"] "seccomp_prctl"
    let cmd ← match ← (← field j "cmd").getStr? with
      | "set_no_new_privs" => pure Seccomp.PrctlCmd.setNoNewPrivs
      | "get_no_new_privs" => pure Seccomp.PrctlCmd.getNoNewPrivs
      | "get_seccomp" => pure Seccomp.PrctlCmd.getSeccomp
      | _ => throw "seccomp_prctl.cmd: expected set_no_new_privs, get_no_new_privs or get_seccomp"
    let arg (name : String) : Except String UInt64 := do
      if (optField j name).isSome then UInt64.ofNat <$> natField j name 18446744073709551615 else pure 0
    return .seccompPrctl cmd #[← arg "arg2", ← arg "arg3", ← arg "arg4", ← arg "arg5"]
  | "seccomp_capdrop" =>
    fields j ["op"]
    return .seccompCapdrop
  | "seccomp_query" =>
    subsetFields j ["op", "cmd", "action", "flags"] "seccomp_query"
    let cmd ← match ← (← field j "cmd").getStr? with
      | "get_action_avail" => pure Seccomp.QueryCmd.getActionAvail
      | "get_notif_sizes" => pure Seccomp.QueryCmd.getNotifSizes
      | _ => throw "seccomp_query.cmd: expected get_action_avail or get_notif_sizes"
    let action ← if (optField j "action").isSome then u32Field j "action" else pure 0
    let flags ← if (optField j "flags").isSome then u32Field j "flags" else pure 0
    return .seccompQuery cmd action flags
  | "wg_set" =>
    fields j (["op", "config"] ++ if (optField j "device").isSome then ["device"] else [])
    return .wgSet { (← parseConfig (← field j "config")) with device := ← parseDevice j }
  | "wg_get" =>
    fields j (["op"] ++ if (optField j "device").isSome then ["device"] else [])
    return .wgGet (← parseDevice j)
  | "wg_get_start" =>
    fields j (["op"] ++ if (optField j "device").isSome then ["device"] else [])
    return .wgGetStart (← parseDevice j)
  | "wg_get_recv" =>
    fields j ["op"]
    return .wgGetRecv
  | "wg_up" =>
    fields j ["op"]
    return .wgUp
  | "wg_netns_close" =>
    fields j ["op"]
    return .wgNetnsClose
  | "wg_observe" =>
    fields j ["op"]
    return .wgObserve
  | "wg_create" =>
    fields j ["op"]
    return .wgCreate
  | "wg_down" =>
    fields j ["op"]
    return .wgDown
  | "wg_delete" =>
    fields j ["op"]
    return .wgDelete
  | "wg_inject" =>
    -- W5: `tos` and `from: "ll"` are optional; W9: the destination `to`
    let obj ← j.getObj?
    if !(obj.all (fun k _ => ["op", "family", "port", "message", "tos", "from", "to"].contains k)
        && obj.contains "family" && obj.contains "port" && obj.contains "message") then
      throw "expected op, family, port, message and optionally tos, from, to"
    let tos ← senderTos j
    let ll ← match j.getObjVal? "from" with
      | .ok v => do
        if (← v.getStr?) != "ll" then throw "from: expected \"ll\""
        pure true
      | .error _ => pure false
    let family ← (← field j "family").getNat?
    if ll && family != 6 then throw "from: only an IPv6 injection is sent from the link-local address"
    if family != 4 && family != 6 then throw "family: expected 4 or 6"
    let port ← natField j "port" 65535
    if port == 0 then throw "port: expected 1-65535"
    let s ← (← field j "message").getStr?
    if s.length == 0 || s.length % 2 != 0 || s.length > 2800 then throw "message: expected 1-1400 bytes of lowercase hex"
    let message ← hexBytes (← field j "message") s.length "message"
    let dest ← match j.getObjVal? "to" with
      | .error _ => pure 0
      | .ok t => match ← t.getStr? with
        | "loopback" => pure 0
        | "wg0" => pure 1
        | "loopback-alias" => if family == 4 then pure 2 else throw "to: loopback-alias is IPv4 only"
        | _ => throw "to: expected loopback, wg0 or loopback-alias"
    return .wgInject family port message tos ll dest
  | "wg_deladdr" =>
    fields j ["op", "family"]
    let family ← (← field j "family").getNat?
    if family != 4 && family != 6 then throw "family: expected 4 or 6"
    return .wgDeladdr family
  | "wg_delroute" =>
    let obj ← j.getObj?
    if !(obj.all fun k _ => ["op", "family", "dst", "plen", "oif", "type", "metric"].contains k) then
      throw "wg_delroute: unexpected field"
    let family ← (← field j "family").getNat?
    if family != 4 && family != 6 then throw "family: expected 4 or 6"
    if obj.size == 2 then return .wgDelroute family false 0 0 0 0 0
    -- lane C: a named route
    if family != 4 then throw "wg_delroute: a named route is IPv4"
    let dst := bigEndian (← hexBytes (← field j "dst") 8 "dst")
    let plen ← natField j "plen" 32
    let oif ← routeOif j
    let typeCode ← routeType j false
    let metric ← optNat j "metric" 4294967295
    return .wgDelroute family true dst plen oif typeCode metric
  | "wg_addroute" =>
    let obj ← j.getObj?
    if !(obj.all fun k _ => ["op", "family", "dst", "plen", "type", "oif", "metric", "mtu", "nlflags"].contains k) then
      throw "wg_addroute: unexpected field"
    let family ← (← field j "family").getNat?
    if family != 4 then throw "family: expected 4 (IPv6 routes keep the environment's rule)"
    let dst := bigEndian (← hexBytes (← field j "dst") 8 "dst")
    let plen ← natField j "plen" 32
    let typeCode ← routeType j true
    let oif ← routeOif j
    let metric ← optNat j "metric" 4294967295
    let mtu ← optNat j "mtu" 65535
    let nlflags ← match j.getObjVal? "nlflags" with
      | .error _ => pure 0
      | .ok f => do
        let arr ← f.getArr?
        let mut n := 0
        for x in arr do
          match ← x.getStr? with
          | "excl" => n := n ||| Net.Fib.NLM_F_EXCL
          | "replace" => n := n ||| Net.Fib.NLM_F_REPLACE
          | "append" => n := n ||| Net.Fib.NLM_F_APPEND
          | _ => throw "nlflags: expected excl, replace or append"
        pure n
    return .wgAddroute dst plen oif typeCode metric mtu nlflags
  | "wg_addaddr" =>
    fields j ["op", "addr", "plen"]
    let addr := bigEndian (← hexBytes (← field j "addr") 8 "addr")
    let plen ← natField j "plen" 32
    return .wgAddaddr addr plen
  | "wg_flood" =>
    -- `messages`: the leading valid-MAC1 initiations the mirror processes and
    -- checks (byte-exact cookie replies). `control` (a mid-flood valid packet
    -- the mirror must NOT model) is a fixture-only field the mirror ignores: it
    -- lands in the discarded region and makes the check fail closed.
    let obj ← j.getObj?
    if !(obj.all (fun k _ => ["op", "count", "port", "family", "messages", "control"].contains k)
        && obj.contains "op" && obj.contains "count" && obj.contains "port") then
      throw "expected op, count, port and optionally family, messages, control"
    -- `family` (optional, default 4): the flood's destination, the v4-mapped
    -- 127.0.0.1 or ::1 (the ratelimiter's IPv6 /64 table, 2026-10-14)
    let family ← match j.getObjVal? "family" with
      | .ok v => do
        let n ← v.getNat?
        if n != 4 && n != 6 then throw "family: expected 4 or 6"
        pure n
      | .error _ => pure 4
    -- B4 (2.4): the flood runs exactly, so its size is bounded by the
    -- handshake ring (MAX_QUEUED_INCOMING_HANDSHAKES, 4096: B1's twins fill
    -- it and drop one send at a full slot) and the report's MAX_BRANCHES;
    -- harness/trace.py has the same bound
    let count ← natField j "count" 4096
    if count == 0 then throw "count: expected 1-4096"
    let port ← natField j "port" 65535
    if port == 0 then throw "port: expected 1-65535"
    let messages ← match j.getObjVal? "messages" with
      | .ok (.arr xs) => xs.toList.mapM fun m => do
          let s ← m.getStr?
          if s.length == 0 || s.length % 2 != 0 || s.length > 2800 then throw "messages: 1-1400 bytes hex each"
          hexBytes m s.length "messages"
      | .ok _ => throw "messages: expected an array"
      | .error _ => pure []
    return .wgFlood count port family messages
  | "wg_batch" =>
    -- W7 (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5): `items`, each
    -- `{kind: "inject", family, port, message}` or `{kind: "xmit", packet}`;
    -- `wait_ms` optional (the guest's wait after the submission)
    let obj ← j.getObj?
    if !(obj.all (fun k _ => ["op", "items", "wait_ms"].contains k) && obj.contains "op" && obj.contains "items") then
      throw "expected op, items and optionally wait_ms"
    let waitMs ← match j.getObjVal? "wait_ms" with
      | .ok v => do
        let n ← v.getNat?
        if n == 0 || n > 4000 then throw "wait_ms: expected 1-4000"
        pure n
      | .error _ => pure 100
    let items ← match j.getObjVal? "items" with
      | .ok (.arr xs) => do
        if xs.size == 0 || xs.size > 1025 then throw "items: expected 1-1025 items"
        xs.toList.mapM fun it => do
          match ← (← field it "kind").getStr? with
          | "inject" =>
            fields it ["kind", "family", "port", "message"]
            let family ← (← field it "family").getNat?
            if family != 4 && family != 6 then throw "items[].family: expected 4 or 6"
            let port ← natField it "port" 65535
            if port == 0 then throw "items[].port: expected 1-65535"
            let s ← (← field it "message").getStr?
            if s.length == 0 || s.length % 2 != 0 || s.length > 2800 then throw "items[].message: expected 1-1400 bytes of lowercase hex"
            let message ← hexBytes (← field it "message") s.length "items[].message"
            pure (Env.BatchItem.inject family port message)
          | "xmit" =>
            fields it ["kind", "packet"]
            let (family, addr, payload, opts) ← parsePacket (← field it "packet")
            pure (Env.BatchItem.xmit family addr payload opts)
          | _ => throw "items[].kind: expected \"inject\" or \"xmit\""
      | .ok _ => throw "items: expected an array"
      | .error _ => throw "items: expected an array"
    return .wgBatch items waitMs
  | "wg_advance" =>
    fields j ["op", "ticks"]
    let ticks ← natField j "ticks" (2 ^ 31)
    if ticks == 0 then throw "ticks: expected 1-2^31"
    return .wgAdvance ticks
  | "wg_xmit" =>
    let obj ← j.getObj?
    if !(obj.all (fun k _ => ["op", "packet", "tos"].contains k) && obj.contains "packet") then
      throw "expected op, packet and optionally tos"
    let tos ← senderTos j   -- W5
    let (family, addr, payload, opts) ← parsePacket (← field j "packet")
    return .wgXmit family addr payload { opts with tos }
  | "wg_set_mtu" =>
    fields j ["op", "mtu"]
    let mtu ← (← field j "mtu").getNat?
    -- the ioctl's `ifr_mtu` is an int the guest fills with `(int)op->a`: a u32
    -- word, negative to the kernel at or above 2^31 (`Env.setMtu`)
    if mtu > 0xFFFFFFFF then throw "mtu: expected 0-4294967295"
    return .wgSetMtu mtu
  | _ => throw "unsupported operation"

private def parseHidden (j : Json) (ops : Nat) : Except String (Array (List HiddenRecord)) := do
  let perOp ← j.getArr?
  if perOp.size != ops then throw "hidden: expected one record list per operation"
  perOp.mapM fun recs => do
    (← recs.getArr?).toList.mapM fun r => do
      let pair ← r.getArr?
      if pair.size != 2 then throw "hidden: expected [site, hex] records"
      let site ← pair[0]!.getNat?
      let s ← pair[1]!.getStr?
      if s.length % 16 != 0 || s.length > 128 then throw "hidden: payload must be whole 8-byte words"
      let bytes ← hexBytes pair[1]! s.length "hidden"
      return { site, bytes }

def parseTrace (j : Json) : Except String Trace := do
  let hasLimit := (j.getObjVal? "rlimit_nofile").isOk
  let hasHidden := (j.getObjVal? "hidden").isOk
  let hasSteer := (j.getObjVal? "steer").isOk
  let hasExpect := (j.getObjVal? "expect").isOk
  let hasArm := (j.getObjVal? "arm_records").isOk
  let hasPlacement := (j.getObjVal? "napi_irq_before_put").isOk
  let hasFixture := (j.getObjVal? "net_fixture").isOk
  let hasArmed := (j.getObjVal? "alloc_armed").isOk
  let hasDst := (j.getObjVal? "dst_cache_records").isOk
  let hasExtension := (j.getObjVal? "domain_extension").isOk
  let hasSeccompChild := (j.getObjVal? "seccomp_child").isOk
  let hasSeccompPrefill := (j.getObjVal? "seccomp_prefill").isOk
  fields j ((if hasLimit then ["version", "id", "ops", "rlimit_nofile"] else ["version", "id", "ops"])
    ++ (if hasHidden then ["hidden"] else []) ++ (if hasSteer then ["steer"] else [])
    ++ (if hasExpect then ["expect"] else []) ++ (if hasArm then ["arm_records"] else [])
    ++ (if hasPlacement then ["napi_irq_before_put"] else [])
    ++ (if hasFixture then ["net_fixture"] else [])
    ++ (if hasArmed then ["alloc_armed"] else [])
    ++ (if hasDst then ["dst_cache_records"] else [])
    ++ (if hasExtension then ["domain_extension"] else [])
    ++ (if hasSeccompChild then ["seccomp_child"] else [])
    ++ (if hasSeccompPrefill then ["seccomp_prefill"] else []))
  -- D3: the arm-record switch qualifies the records, so it comes with them
  if hasArm && !hasHidden then throw "arm_records: only with hidden records"
  let armRecords ← if hasArm then (← field j "arm_records").getBool? else pure false
  let dstCacheRecords ← if hasDst then (← field j "dst_cache_records").getBool? else pure true
  -- The declared failslab-style extension (docs/2026-10-05-a-alloc.md,
  -- section 3, [USER 2026-10-06]): the trace forces task-context allocation
  -- failures; the host checks the schedule, the mirror only its form.
  if hasExtension then
    if (← (← field j "domain_extension").getStr?) != "failslab" then throw "domain_extension: expected \"failslab\""
    if !hasSteer then throw "domain_extension: only a steered trace declares it"
  let rlimit ← if hasLimit then natField j "rlimit_nofile" 1024 else pure 32
  if rlimit < 8 then throw "rlimit_nofile outside 8..1024"
  if (← (← field j "version").getNat?) != 1 then throw "unsupported trace version"
  let id ← (← field j "id").getStr?
  if id.isEmpty || id.length > 80 || !id.toList.all (fun c =>
      c.isAlphanum && c.toNat < 128 || c == '_' || c == '-' || c == '.') then
    throw "invalid trace identifier"
  let rawOps ← (← field j "ops").getArr?
  if rawOps.isEmpty || rawOps.size > 64 then throw "trace length outside 1..64"
  let mut ops := #[]
  let mut pauses := #[]
  for j in rawOps do
    -- `pause_ms` (1-20) may accompany any operation; the rest is the
    -- operation's own exact field set
    let obj ← j.getObj?
    let (j, pause) ← match obj.get? "pause_ms" with
      | some v => do
        let n ← v.getNat?
        if n < 1 || n > PAUSE_MS_MAX then throw "pause_ms outside 1..20"
        pure (Json.obj (obj.erase "pause_ms"), n)
      | none => pure (j, 0)
    ops := ops.push (← parseOperation j ops)
    pauses := pauses.push pause
  let hidden ← if hasHidden then some <$> parseHidden (← field j "hidden") ops.size else pure none
  let steer ← if hasSteer then (← (← field j "steer").getArr?).toList.mapM fun e => do
      let pair ← e.getArr?
      if pair.size != 2 then throw "steer: expected [site, value] entries"
      let label ← pair[0]!.getStr?
      let v ← pair[1]!.getStr?
      if v == "draw" then return (label, none)
      if v.length == 0 || v.length % 2 != 0 || v.length > 80 then throw "steer: value hex"
      return (label, some (← hexBytes pair[1]! v.length "steer"))
    else pure []
  let napiBeforePut ← if hasPlacement then
      (← (← field j "napi_irq_before_put").getArr?).toList.mapM fun b => b.getBool?
    else pure []
  -- The ceiling on the placement vector is the records': `Env.napiIrqExit`
  -- opens a poll only where the next record is a NET_RX section start, so
  -- the vector can name no more polls than the records hold section starts
  -- (the W7 tier's receive twin opens about a thousand); without records
  -- there is no open placement. The former bound of 8 was a budget from
  -- when open placements were rare, and it refused the check's selection
  -- run on a loaded host (2026-10-15).
  let netRxStarts := match hidden with
    | some perOp => perOp.foldl (fun n recs =>
        n + (recs.filter (·.site == (HiddenSite.sectionStart .netRx).info.id)).length) 0
    | none => 0
  if napiBeforePut.length > netRxStarts then
    throw "napi_irq_before_put: more entries than NET_RX section starts in the records"
  -- L: "bare"; W8: "foreign-creator"; W4: {"routes": [...]}
  let (bare, foreign, routes) ← if hasFixture then do
      let f ← field j "net_fixture"
      match f.getStr? with
      | .ok "bare" => pure (true, false, [])
      | .ok "foreign-creator" => pure (false, true, [])
      | .ok _ => throw "net_fixture: expected \"bare\", \"foreign-creator\" or {\"routes\": [...]}"
      | .error _ => do
        -- W4: the fixture's routes into wg0 with an MTU (section 6)
        fields f ["routes"]
        let rs ← (← (← field f "routes").getArr?).toList.mapM fun r => do
          fields r ["family", "dst", "mtu"]
          let family ← (← field r "family").getNat?
          if family != 4 && family != 6 then throw "net_fixture.routes[].family: expected 4 or 6"
          let addr := bigEndian (← hexBytes (← field r "dst") (if family == 4 then 8 else 32) "net_fixture.routes[].dst")
          let mtu ← (← field r "mtu").getNat?
          if mtu < 68 || mtu > 65535 then throw "net_fixture.routes[].mtu: expected 68-65535"
          pure (family, addr, mtu)
        if rs.isEmpty || rs.length > 8 then throw "net_fixture.routes: expected 1-8 routes"
        pure (false, false, rs)
    else pure (false, false, [])
  let allocArmed ← if hasArmed then (← (← field j "alloc_armed").getArr?).toList.mapM fun e => do
      let label ← e.getStr?
      if !(AllocSite.all.any fun s => s.info.label == label && s.info.count != .cut) then
        throw s!"alloc_armed: {label} is not a consumed allocation site"
      pure label
    else pure []
  if hasArmed && !hasHidden then throw "alloc_armed: an armed run carries its records"
  let seccompChild ← if hasSeccompChild then (← field j "seccomp_child").getBool? else pure false
  let seccompPrefill ← if hasSeccompPrefill then (← field j "seccomp_prefill").getNat? else pure 0
  let trace : Trace := { id, ops, rlimit, hidden, steer, armRecords, napiBeforePut, allocArmed, pauses, bare, foreign, routes, dstCacheRecords, seccompChild, seccompPrefill }
  -- seccomp design 5: the prefill fixture is the trace process's, outside every
  -- window: never with a network fixture or a steering schedule
  if hasSeccompPrefill && (seccompPrefill == 0 || seccompPrefill > Leanux.Seccomp.Prefill.PREFILL_MAX) then
    throw s!"seccomp_prefill: expected 1..{Leanux.Seccomp.Prefill.PREFILL_MAX}"
  if seccompPrefill > 0 && (trace.net || !steer.isEmpty) then
    throw "seccomp_prefill: never with a network fixture or a steering schedule"
  if (bare || foreign || !routes.isEmpty) && !trace.net then throw "net_fixture: only a network trace has a network fixture"
  -- seccomp design 5: descriptor 8 is the child's KCOV or W8's injector, never both
  if seccompChild && trace.net then throw "seccomp_child: exclusive with a network fixture"
  if trace.ops.any (fun | .seccompProbe _ _ .child _ => true | _ => false) && !seccompChild then
    throw "seccomp_probe in a child needs the seccomp_child fixture"
  if foreign && rlimit < 10 then throw "net_fixture: the foreign-creator fixture needs rlimit_nofile >= 10"
  -- W2 (4.2): the stepped dump socket at fd 8 (reserved 0..8); L's
  -- temporary rtnetlink socket then lands at 9. The foreign-creator fixture
  -- holds 8 and 9 itself, so the two are exclusive.
  if trace.stepped && foreign then throw "a stepped dump and the foreign-creator fixture both need descriptor 8"
  if trace.stepped && rlimit < 9 then throw "a stepped dump needs rlimit_nofile >= 9"
  if trace.stepped && rlimit < 10 && ops.any (fun | .wgCreate | .wgDelete => true | _ => false) then
    throw "a stepped dump with wg_create or wg_delete needs rlimit_nofile >= 10"
  -- the fixture's holders are reserved descriptors like 0..7 (`reservedFds`):
  -- a literal that names one would alias or close the harness's apparatus
  -- (a retained alias of W8's pin keeps the creating namespace alive past
  -- `wg_netns_close`, whose cleanup runs only in that operation's wait)
  let reserved := reservedFds foreign trace.stepped seccompChild
  for op in ops do
    for fd in op.descriptors do
      if let .literal n := fd then
        if 0 ≤ n && n < reserved then
          throw s!"descriptor literal {n} is the fixture's (reserved 0..{reserved - 1})"
  return trace

/-! ## Harness fixture and trace execution

The guest child (harness/guest.c) runs each trace in a fresh forked process:
descriptors 0-2 are the inherited console (one shared `struct file`), 3 is
KCOV (also memory-mapped), 4-7 are separately opened /dev/null files, and
RLIMIT_NOFILE is 32. The fork gave the child its own files_struct
(`count = 1`) with the embedded 64-slot table. Allocation history leaves
`next_fd = 8`. Fixture files carry references held outside the trace.

The network fixture (traces with a WireGuard operation) runs in a new network
namespace holding `lo` (up), `sit0` (ifindex 2) and, unless the trace asks for
the bare fixture (L), a down WireGuard device `wg0` at ifindex 3, created
before the trace (its ratelimiter reference taken, its draws unknown).
Descriptors 4 and 5 are UDP listeners on 127.0.0.1 and ::1 at `LISTEN_PORT`,
6 a dual-stack UDP sender, and 7 a generic-netlink socket, instead of
/dev/null. -/

/-- A fixture file. Its mode, operations and inode are outside the slice: any
    operation that consults them is `unsupported`. -/
def fixtureFile (name : String) (refs : Nat) : File :=
  -- W8: the pin is `open("/proc/self/ns/net", O_RDONLY)`; the others are
  -- read-write (sockets, the console, the KCOV descriptor)
  if name == "netns-pin" then
    { fFlags := O_RDONLY, fMode := FMODE_READ ||| FMODE_OPENED,
      fCount := refs, fOp := some (.fixture name), fInode := some (.fixture name) }
  else
    { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED,
      fCount := refs, fOp := some (.fixture name), fInode := some (.fixture name) }

/-- The trace process at the start (the task store): its file table over the
    reserved descriptors, the rlimit, SIGPIPE blocked (P design section 6)
    and no pending signal; no child; `current` is the task. -/
def initialTasks (rlimit : Nat) (foreign : Bool := false) (stepped : Bool := false) (seccompChild : Bool := false) : TaskWorld :=
  let reserved := reservedFds foreign stepped seccompChild
  let slot (fd : Nat) : Option FileId :=
    if fd < 3 then some 0 else if fd < reserved then some (fd - 2) else none
  let slots := (List.range NR_OPEN_DEFAULT).toArray
  { task := {
      files := { count := 1, resizeInProgress := false, nextFd := reserved,
                 fdt := { maxFds := NR_OPEN_DEFAULT, fd := slots.map slot,
                          openFds := slots.map (· < reserved), closeOnExec := slots.map fun _ => false } }
      rlimitNofile := rlimit
      blocked := sigmask SIGPIPE, pending := 0 } }

/-- WireGuard's initial world (the state split, section 2): the fixture's
    wg0 in a network trace that is not bare; L: the netns's ifindex cursor
    (lo 1, sit0 2, the fixture's wg0 3) and the ratelimiter's reference
    count (the fixture's wg0 holds one; every earlier trace process deleted
    its devices). -/
def initialWG (net : Bool := false) (bare : Bool := false) : WGWorld :=
  { dev := if net && !bare then some { ifindex := 3, ifname := "wg0" } else none,
    netIfindexNext := if net && !bare then 4 else 3,
    ratelimiter := { refcnt := if net && !bare then 1 else 0 } }

/-- The file layer's stores at the start (the state split, phase 2): the
    fixture's files over the reserved descriptors, the environment facts and
    the sysctl defaults, as the former `initialKernel` held them before the split. -/
def initialFS (net : Bool := false) (foreign : Bool := false) (stepped : Bool := false)
    (seccompChild : Bool := false) : FSWorld :=
  -- W8: the foreign-creator fixture adds the injector (8) and the pin (9);
  -- W2: a stepped trace adds the dump socket (8); seccomp (design 6.2 rule
  -- 2): the children's KCOV descriptor (8); the validator keeps the two apart
  let reserved := reservedFds foreign stepped seccompChild
  let files : Std.TreeMap FileId File := Std.TreeMap.ofList
    ([(0, fixtureFile "console" 4),   -- fds 0-2 plus init's references
      (1, fixtureFile "kcov" 2)] ++    -- fd 3 plus the coverage mapping
     (List.range (reserved - 4)).map fun i =>
       (i + 2, fixtureFile (if !net then (if seccompChild && i == 4 then "kcov-child" else "/dev/null") else
         match i with
         | 0 => "udp-listener-127.0.0.1" | 1 => "udp-listener-::1" | 2 => "udp-sender"
         | 3 => "generic-netlink" | 4 => if stepped then "generic-netlink-dump" else "udp-injector"
         | _ => "netns-pin") 1))
  {
    files, nextFile := if foreign then 8 else if stepped || seccompChild then 7 else 6, ctxs := {}, nextCtx := 0,
    idaUsed := {},
    -- Environment facts: the system-wide open-file count and limit are not
    -- observed; the guest has few files open, far below any boot-sized limit.
    nrFiles := if foreign then 8 else if stepped || seccompChild then 7 else 6, maxFiles := 1000000, anonInodeInodeErr := false,
    -- Pipes (P design section 5): sysctl defaults, and `root_user`'s
    -- `pipe_bufs` at its baseline of 0 (no pipes outside the trace)
    pipeMaxSize := 1048576, pipeUserPagesSoft := 16384, pipeUserPagesHard := 0, user := { pipeBufs := 0 },
    -- epoll: the fixture facts of Leanux/Env.lean (the warm-up's relative
    -- counter, the boot's max_user_watches)
    loopCheckGen := Env.LOOP_CHECK_GEN_BASE, maxUserWatches := Env.MAX_USER_WATCHES }

/-- The harness environment for the pipe sites (`EnvSite`): every allocation
    and user-memory access succeeds. -/
def harnessEnv : EnvSite → Nat → Bool := fun _ _ => true

/-- A descriptor argument's value. `ends` holds each operation's `pipe2`
    pair (`fds`); a failed producer resolves to -1 (harness/guest.c). -/
def resolveFD (results : Array Int) (ends : Array (Option (Nat × Nat))) : FDArg → Int
  | .literal n => n
  | .ref i =>
    match results[i]? with
    | some n => if n < 0 then -1 else n
    | none => -1 -- Only reachable when bypassing parseTrace.
  | .pipe i e =>
    match results[i]?, ends[i]? with
    | some 0, some (some (r, w)) => if e == 0 then r else w
    | _, _ => -1

private def hexByte (n : Nat) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[n / 16 % 16]!, digits[n % 16]!]

def hexBytesOf (bs : ByteArray) : String :=
  String.join (bs.toList.map fun b => hexByte b.toNat)

/-- The caller's write buffer for operation `index` (P design section 6),
    which harness/guest.c fills identically: bytes 0-7 are `value`
    little-endian (eventfd writes read them), and byte `k ≥ 8` is
    `(7·index + 13·k + 17·(k >> 8)) mod 256`. At least 8 bytes long. -/
def writeBuffer (index : Nat) (value : UInt64) (count : Nat) : ByteArray :=
  ByteArray.mk ((List.range (max count 8)).toArray.map fun k =>
    if k < 8 then UInt8.ofNat (value.toNat / 256 ^ k % 256)
    else UInt8.ofNat ((7 * index + 13 * k + 17 * (k >>> 8)) % 256))

/-- The `digest` observation field of a read (P design section 6, Q1):
    BLAKE2s-256 over all `ret` bytes when `ret > 0`, else `null`; harness/guest.c
    computes the same. -/
def readDigest (out : Option ByteArray) (ret : Int) : Json :=
  match out with
  | some bs => if ret > 0 then toJson (hexBytesOf (ByteArray.mk (WG.blake2s 32 [] (bs.extract 0 ret.toNat).toList).toArray)) else .null
  | none => .null

/-- The `sigpipe` observation field of a write: whether `SIGPIPE` is pending
    in the task after the call (the guest's `sigpending()` after each write). -/
def writeSigpipe (t : TaskWorld) : Json :=
  toJson (if sigismember t.task.pending SIGPIPE then (1 : Nat) else 0)

def toSyscall (results : Array Int) (ends : Array (Option (Nat × Nat))) (index : Nat) : Operation → Syscall
  | .eventfd2 init flags => .eventfd2 init flags
  | .dup fd => .dup (uint (resolveFD results ends fd))
  | .dup3 fd newfd flags => .dup3 (uint (resolveFD results ends fd)) (uint (resolveFD results ends newfd)) flags
  | .close fd => .close (uint (resolveFD results ends fd))
  | .read fd count => .read (uint (resolveFD results ends fd)) count
  | .write fd count value => .write (uint (resolveFD results ends fd)) count (writeBuffer index value count)
  | .fcntl fd cmd arg => .fcntl (uint (resolveFD results ends fd)) cmd arg.toUInt64
  | .pipe2 flags => .pipe2 flags
  | .epollCreate1 flags => .epollCreate1 flags
  -- `int op` and `int fd` from the wire's u32s: two's complement
  | .epollCtl epfd cmd fd events data =>
    let int32 (u : UInt32) : Int := if u.toNat ≥ 2 ^ 31 then (u.toNat : Int) - 2 ^ 32 else u.toNat
    .epollCtl (uint (resolveFD results ends epfd)) (int32 cmd) (resolveFD results ends fd) events data
  | .epollWait epfd maxevents timeout => .epollWait (uint (resolveFD results ends epfd)) maxevents timeout
  | .wgSet attrs => .wgSet attrs
  | .wgGet device => .wgGet device
  | .wgGetStart device => .wgGetStart device
  | .wgGetRecv => .wgGetRecv
  | .wgUp => .wgUp
  | .wgXmit family addr payload opts => .wgXmit family addr payload opts
  | .wgSetMtu mtu => .wgSetMtu mtu
  | .wgObserve => .wgObserve
  | .wgInject family port message tos ll dest => .wgInject family port message tos ll dest
  | .wgDeladdr family => .wgDeladdr family
  | .wgDelroute family named dst plen oif typeCode metric => .wgDelroute family named dst plen oif typeCode metric
  | .wgAddroute dst plen oif typeCode metric mtu nlflags => .wgAddroute dst plen oif typeCode metric mtu nlflags
  | .wgAddaddr addr plen => .wgAddaddr addr plen
  | .wgFlood count port family messages => .wgFlood count port family messages
  | .wgBatch items waitMs => .wgBatch items waitMs
  | .wgAdvance ticks => .wgAdvance ticks
  | .wgCreate => .wgCreate
  | .wgDown => .wgDown
  | .wgDelete => .wgDelete
  | .wgNetnsClose => .wgNetnsClose
  | .seccompInstall via flags filter len bad mode => .seccompInstall via flags filter len bad mode
  | .seccompProbe nr args where_ strict => .seccompProbe nr args where_ strict
  | .seccompPrctl cmd args => .seccompPrctl cmd args
  | .seccompCapdrop => .seccompCapdrop
  | .seccompQuery cmd action flags => .seccompQuery cmd action flags

/-- Lane C: the boot trie of a network trace's fixture namespace (`lo` up),
    for `leanux-model --fib-boot` and the harness's expected fixture facts. -/
def fibBootJson : Except Stop Json := do
  let world : World := { fs := initialFS true, wg := initialWG true, tasks := initialTasks 32,
                         ambient := { env := harnessEnv, timing := Env.timing } }
  let (_, w) ← (liftWG (liftRouting Net.Fib.bootTables)).run world
  return Net.Fib.shape w.wg.routing

/-- Run a trace. A `Stop` is returned with the operation index: the mirror
    never reports an observation for a path it does not model. -/
def executeTrace (trace : Trace) (placeholders : Bool := false) : Except (Nat × Stop) Json := do
  let ambient : Ambient := { env := harnessEnv, timing := Env.timing,
                             allocArmed := trace.allocArmed,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let mut world : World := { ambient,
                             fs := initialFS trace.net trace.foreign trace.stepped trace.seccompChild,
                             tasks := initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild,
                             wg := { initialWG trace.net trace.bare with
                                     portBound := Env.portBound,
                                     fixtureNetDevices := Env.fixtureNetDevices,
                                     dstCacheRecords := trace.dstCacheRecords,
                                     routing := { foreignCreator := trace.foreign } },
                             fixture := { netnsCHolders := if trace.foreign then [9, 8, 5, 4] else [],
                                          routes := trace.routes,
                                          napiBeforePut := trace.napiBeforePut } }
  -- the seccomp prefill fixture (design 5): the chain the guest installed before the window
  if trace.seccompPrefill > 0 then
    match Env.seccompPrefill trace.seccompPrefill world.seccomp world.tasks with
    | .ok (seccomp, tasks) => world := { world with seccomp, tasks }
    | .error e => throw (0, .invariant e)
  -- lane C: the fixture namespaces' IPv4 tables at boot (`lo` up in each),
  -- built by the C's own sequence outside every window (the design note,
  -- 9.3); its steps are discarded with the first operation's reset
  if trace.net then
    let boot : M Unit := do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
    match boot.run world with
    | .ok (_, w) => world := { w with ambient := { w.ambient with steps := #[], envCalls := [] } }
    | .error e => throw (0, e)
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
    world := { world with ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) },
                          fixture := { world.fixture with hiddenAhead := ahead }, wg := { world.wg with netRxRaised := false } }
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
    -- dispatch order: a device-level unit whose PENDING bit is set at the end
    -- of an operation is a dispatch the kernel runs inside the guest's wait
    -- (`Env.pendingDevice`), so its section belongs to this operation's
    -- records; with records, its absence is a hidden mismatch (campaign 2's
    -- request 4, 2026-10-19). Without records the scheduler runs every unit
    -- it knows in the fixed order, pending ones included (`Env.schedule`), so
    -- a unit still pending has no run site in either mode: a placeholder run
    -- that leaves one is a mirror invariant, never a pass (campaign 2's
    -- namespace-pin finding, 2026-10-20: the refusal sat in the record branch
    -- only, and the placeholder run alone accepted a cleanup queued by a
    -- retained alias of the pin).
    if let i :: _ := w.ambient.pendingWork then
      let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
      if w.ambient.hidden.isSome then
        throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
      else
        throw (index, .invariant s!"{name} is pending at the end of the operation (the fixed order ran no dispatch for it)")
    if w.wg.netRxRaised then
      throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
    world := w
    results := results.push ret
    ends := ends.push (if ret == 0 then w.fs.userFds else none)
    -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
    -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
    let bytes := match op, w.fs.userOut with
      | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
      | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
      | _, _ => ""
    -- pipe2: the pair copied to the caller, or null on failure; a read's
    -- digest; a write's sigpipe (P design section 6)
    let fds : List (String × Json) := match op with
      | .pipe2 _ => [("fds", match w.fs.userFds with
          | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
          | none => .null)]
      | .read .. => [("digest", readDigest w.fs.userOut ret)]
      | .epollWait .. => [("digest", readDigest w.fs.userOut (ret * 12))]
      | .write .. => [("sigpipe", writeSigpipe w.tasks)]
      | _ => []
    let device := w.ambient.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ fds ++ device))
    for s in w.ambient.steps do
      -- W7 stream H: the NET_RX section ordinal of a step inside one
      let fields := [("index", toJson index), ("label", toJson s.label)]
        ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
      branches := branches.push (Json.mkObj (match s.operands, s.excluded with
        | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
        | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
        | none, none => fields))
    for symbol in w.ambient.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  -- a placement the check chose must have been met
  if world.fixture.napiBeforePut.any id then
    throw (results.size - 1, .invariant "napi_irq_before_put names more NAPI polls than the trace has")
  -- the domain filter: a schedule entry for an allocation site that the
  -- mirror never met would be left over in the kernel
  if world.ambient.hiddenPlaceholders && world.ambient.steerValues.any (fun e => world.ambient.allocSteered.contains e.1) then
    throw (trace.ops.size - 1, .outsideDomain "steer" "allocation schedule entries beyond the encounters")
  -- D3: the timer sections the environment ran (`fired:<symbol>`
  -- expectations), present only when one ran
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))

/-- The hidden-input site table, for the check's call-site cross-check. -/
def hiddenSitesJson : Json :=
  .arr (HiddenSite.all.map fun s =>
    let i := s.info
    Json.mkObj [("id", toJson i.id), ("label", toJson i.label), ("kind", toJson i.kind),
      ("file", toJson i.file), ("line", toJson i.line), ("len", toJson i.len),
      ("role", toJson i.role.name)]).toArray

def spanJson (s : Span) : Json :=
  Json.mkObj [("file", toJson s.file), ("lo", toJson s.lo), ("hi", toJson s.hi)]

/-- The decision table, for the check's KCOV comparison. -/
def decisionsJson : Json :=
  .arr (Decision.all.map fun d =>
    let i := d.info
    Json.mkObj [("label", toJson i.label), ("file", toJson i.file), ("line", toJson i.line),
      ("when_true", .arr (i.whenTrue.map spanJson).toArray),
      ("when_false", .arr (i.whenFalse.map spanJson).toArray),
      ("terminal", .arr (i.terminal.map toJson).toArray),
      ("repeatable", toJson d.repeatable),
      ("comparison", match d.comparison with
        | some c => Json.mkObj [("rel", toJson c.rel.name), ("const_rhs", toJson c.constRhs),
            ("site", match c.site with | some l => toJson s!"{i.file}:{l}" | none => .null),
            ("assigned", toJson c.assigned)]
        | none => .null)]).toArray

/-! The Send audit's F1 (2026-10-15), held at compile time. At the encrypt
    worker's ring poll the pending NET_RX runs after `ptr_ring_consume_bh`'s
    discard (send.c:293; ptr_ring.h:264-303), so a poll that produces into the
    ring (a key confirmation's flush of staged packets) at a physically full
    ring finds the slot the batch rule has just cleared, as Linux does. The
    instance: fifteen items consumed without a clearing (tail 0, head 15,
    slots 0 to 14 still occupied), then 1009 produced, the producer back at
    the occupied slot 0; the poll's produce at the next ring poll succeeds in
    the C's order and met the occupied slot (`-EPIPE`, the list dropped) in
    the mirror's former order. The schedule needs the 17.17 placement with a
    full ring, which no capture holds; the instance is the state itself. -/
private def f1Ring : WG.PtrRing (List WG.SkbId) :=
  let r0 := (List.range 15).foldl (fun r i => r.produce [i]) (WG.PtrRing.init WG.MAX_QUEUED_PACKETS)
  let r1 := (List.range 15).foldl (fun r _ => r.consume.2) r0
  (List.range 1009).foldl (fun r i => r.produce [100 + i]) r1

private def f1World : World :=
  { fs := initialFS, wg := { dev := some { ifindex := 3, ifname := "wg0", encryptQueue := f1Ring } }, tasks := initialTasks 8,
    ambient := { env := harnessEnv, timing := { advanceWait := 0, traceBound := 0 } } }

/-- The poll's produce (`wg_queue_enqueue_per_device_and_peer`, queueing.h:174):
    `-EPIPE` at a full ring, else the item in the producer's slot. -/
private def f1Poll : M Unit := do
  let d ← WG.getDev
  if d.encryptQueue.full then return
  WG.modifyDev fun d => { d with encryptQueue := d.encryptQueue.produce [9999] }

#guard f1Ring.full
#guard f1Ring.consumerHead == 15 && f1Ring.consumerTail == 0 && f1Ring.producer == 0
#guard match (WG.encryptRingPoll f1Poll).run f1World with
  | .ok (some [100], w) => (w.wg.dev.map fun d => (d.encryptQueue.slots[0]?).getD none) == some (some [9999])
  | _ => false

end Leanux.Runner
