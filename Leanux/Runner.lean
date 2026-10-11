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
  | wgSet (attrs : WG.DeviceAttrs)
  | wgGet
  | wgUp
  | wgXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
  /-- W4 (docs/2026-10-06-w4-w7-transmit-bulk.md section 6): `SIOCSIFMTU` on wg0. -/
  | wgSetMtu (mtu : Nat)
  | wgObserve
  | wgInject (family port : Nat) (message : List UInt8)
  /-- E-B: an io_uring flood of `count` invalid-MAC1 initiations to wg0's port,
      with `messages` valid-MAC1 initiations submitted first (processed under
      load via the queue depth, their cookie replies checked byte-exact);
      docs/2026-10-05-e-dos.md §8. -/
  | wgFlood (count port : Nat) (messages : List (List UInt8))
  /-- W7: an io_uring batch of injects and transmits (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5). -/
  | wgBatch (items : List Env.BatchItem) (waitMs : Nat)
  /-- D3: the virtual time advance (harness/trace.py `wg_advance`). -/
  | wgAdvance (ticks : Nat)
  /-- L (docs/2026-10-05-l-lifecycle.md): wg0's lifecycle. -/
  | wgCreate
  | wgDown
  | wgDelete
  deriving Repr

/-- The operations a `{"ref": i}` may name. -/
def Operation.isProducer : Operation → Bool
  | .eventfd2 .. | .dup .. | .dup3 .. => true
  | _ => false

/-- The operations a `{"pipe": i, "end": e}` may name. -/
def Operation.isPipe : Operation → Bool
  | .pipe2 _ => true
  | _ => false

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
  /-- The check's choice for each NAPI poll placement the records leave open
      (`World.napiBeforePut`). -/
  napiBeforePut : List Bool := []
  /-- `"net_fixture": "bare"` (L): the network fixture without wg0. -/
  bare : Bool := false
  /-- W4: `"net_fixture": {"routes": [...]}`, the routes the fixture adds into
      wg0 at every `wg_up` (family, destination, MTU): `World.routes`. -/
  routes : List (Nat × Nat × Nat) := []
  /-- The allocation sites the run armed (the check adds them with the
      records): their outcomes are consumed from the records. -/
  allocArmed : List String := []
  /-- Each operation's `pause_ms` (0 when absent): a fixture sleep before the
      operation's coverage window, ignored by the mirror (only the clock
      advances). -/
  pauses : Array Nat := #[]
  deriving Repr

/-- The network fixture runs for traces with a WireGuard operation
    (harness/trace.py `uses_wireguard`). -/

def Trace.net (t : Trace) : Bool :=
  t.ops.any fun
    | .wgSet _ | .wgGet | .wgUp | .wgXmit .. | .wgObserve | .wgInject .. | .wgAdvance _
    | .wgFlood _ _ _ | .wgCreate | .wgDown | .wgDelete | .wgSetMtu _ | .wgBatch _ _ => true
    | _ => false

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

private def parseValue (j : Json) : Except String UInt64 := do
  let s ← (← field j "value").getStr?
  let some n := s.toNat? | throw "write value must be decimal"
  if toString n != s || n > 18446744073709551615 then
    throw "write value must be canonical UInt64 decimal"
  return UInt64.ofNat n


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

private def subsetFields (j : Json) (allowed : List String) (what : String) : Except String Unit := do
  let obj ← j.getObj?
  if !obj.all (fun key _ => allowed.contains key) then throw s!"{what}: fields must be a subset of {allowed}"

private def optField (j : Json) (name : String) : Option Json := (j.getObjVal? name).toOption

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

private def parsePeer (j : Json) (i : Nat) : Except String WG.PeerAttrs := do
  let what := s!"config.peers[{i}]"
  subsetFields j ["public_key", "remove", "update_only", "replace_allowed_ips", "preshared_key",
    "endpoint", "keepalive", "allowed_ips"] what
  let publicKey ← hexBytes (← field j "public_key") 64 s!"{what}.public_key"
  let flags := (if ← boolField j "remove" then WG.WGPEER_F_REMOVE_ME else 0) |||
    (if ← boolField j "update_only" then WG.WGPEER_F_UPDATE_ONLY else 0) |||
    (if ← boolField j "replace_allowed_ips" then WG.WGPEER_F_REPLACE_ALLOWEDIPS else 0)
  let presharedKey ← (optField j "preshared_key").mapM (hexBytes · 64 s!"{what}.preshared_key")
  let endpoint ← (optField j "endpoint").mapM fun e => do
    let (family, addr, len, port) ← address e true s!"{what}.endpoint"
    -- sizeof(struct sockaddr_in) or sizeof(struct sockaddr_in6)
    pure ({ len := if len == 4 then 16 else 28, family, addr, port } : WG.EndpointAttr)
  let keepalive ← (optField j "keepalive").mapM fun _ => natField j "keepalive" 65535
  let allowedIps ← (optField j "allowed_ips").mapM fun a => do
    let ips ← a.getArr?
    if ips.size > 32 then throw s!"{what}.allowed_ips: expected at most 32 entries"
    ips.toList.mapIdxM fun k ip => do
      let (family, addr, addrLen, cidr) ← address ip false s!"{what}.allowed_ips[{k}]"
      pure ({ family, addr, addrLen, cidr } : WG.AllowedIpAttrs)
  return { publicKey, presharedKey, flags := if flags != 0 then some flags else none,
           endpoint, keepalive, allowedIps }

private def parseConfig (j : Json) : Except String WG.DeviceAttrs := do
  subsetFields j ["private_key", "listen_port", "fwmark", "replace_peers", "peers"] "config"
  let privateKey ← (optField j "private_key").mapM (hexBytes · 64 "config.private_key")
  let listenPort ← (optField j "listen_port").mapM fun _ => natField j "listen_port" 65535
  let fwmark ← (optField j "fwmark").mapM fun _ => natField j "fwmark" 4294967295
  let replace ← boolField j "replace_peers"
  let peers ← (optField j "peers").mapM fun p => do
    let ps ← p.getArr?
    if ps.size > 16 then throw "config.peers: expected at most 16 peers"
    ps.toList.mapIdxM fun i peer => parsePeer peer i
  return { flags := if replace then some WG.WGDEVICE_F_REPLACE_PEERS else none,
           privateKey, listenPort, fwmark, peers }

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
                               || addr / 2 ^ 32 == 0xffff)
  if bad4 || bad6 then throw "packet.dst: an address the sender does not route into wg0"
  -- a gso_size on IPv6 is beyond the WireGuard boundary: the mirror's
  -- `Env.xmitPackets` answers `unsupported` (the boundary control wc_gso_ipv6)
  return (family, addr, payload, { gsoSize, probe, routeMtu := none })

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
  | "wg_set" =>
    fields j ["op", "config"]
    return .wgSet (← parseConfig (← field j "config"))
  | "wg_get" =>
    fields j ["op"]
    return .wgGet
  | "wg_up" =>
    fields j ["op"]
    return .wgUp
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
    fields j ["op", "family", "port", "message"]
    let family ← (← field j "family").getNat?
    if family != 4 && family != 6 then throw "family: expected 4 or 6"
    let port ← natField j "port" 65535
    if port == 0 then throw "port: expected 1-65535"
    let s ← (← field j "message").getStr?
    if s.length == 0 || s.length % 2 != 0 || s.length > 2800 then throw "message: expected 1-1400 bytes of lowercase hex"
    let message ← hexBytes (← field j "message") s.length "message"
    return .wgInject family port message
  | "wg_flood" =>
    -- `messages`: the leading valid-MAC1 initiations the mirror processes and
    -- checks (byte-exact cookie replies). `control` (a mid-flood valid packet
    -- the mirror must NOT model) is a fixture-only field the mirror ignores: it
    -- lands in the discarded region and makes the check fail closed.
    let obj ← j.getObj?
    if !(obj.all (fun k _ => ["op", "count", "port", "messages", "control"].contains k)
        && obj.contains "op" && obj.contains "count" && obj.contains "port") then
      throw "expected op, count, port and optionally messages, control"
    let count ← natField j "count" (2 ^ 20)
    if count == 0 then throw "count: expected 1-2^20"
    let port ← natField j "port" 65535
    if port == 0 then throw "port: expected 1-65535"
    let messages ← match j.getObjVal? "messages" with
      | .ok (.arr xs) => xs.toList.mapM fun m => do
          let s ← m.getStr?
          if s.length == 0 || s.length % 2 != 0 || s.length > 2800 then throw "messages: 1-1400 bytes hex each"
          hexBytes m s.length "messages"
      | .ok _ => throw "messages: expected an array"
      | .error _ => pure []
    return .wgFlood count port messages
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
    fields j ["op", "packet"]
    let (family, addr, payload, opts) ← parsePacket (← field j "packet")
    return .wgXmit family addr payload opts
  | "wg_set_mtu" =>
    fields j ["op", "mtu"]
    let mtu ← (← field j "mtu").getNat?
    if mtu > 65535 then throw "mtu: expected 0-65535"
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
  let hasExtension := (j.getObjVal? "domain_extension").isOk
  fields j ((if hasLimit then ["version", "id", "ops", "rlimit_nofile"] else ["version", "id", "ops"])
    ++ (if hasHidden then ["hidden"] else []) ++ (if hasSteer then ["steer"] else [])
    ++ (if hasExpect then ["expect"] else []) ++ (if hasArm then ["arm_records"] else [])
    ++ (if hasPlacement then ["napi_irq_before_put"] else [])
    ++ (if hasFixture then ["net_fixture"] else [])
    ++ (if hasArmed then ["alloc_armed"] else [])
    ++ (if hasExtension then ["domain_extension"] else []))
  -- D3: the arm-record switch qualifies the records, so it comes with them
  if hasArm && !hasHidden then throw "arm_records: only with hidden records"
  let armRecords ← if hasArm then (← field j "arm_records").getBool? else pure false
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
  if napiBeforePut.length > 8 then throw "napi_irq_before_put: more than 8 entries"
  let (bare, routes) ← if hasFixture then do
      let f ← field j "net_fixture"
      match f.getStr? with
      | .ok "bare" => pure (true, [])
      | .ok _ => throw "net_fixture: expected \"bare\" or {\"routes\": [...]}"
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
        pure (false, rs)
    else pure (false, [])
  let allocArmed ← if hasArmed then (← (← field j "alloc_armed").getArr?).toList.mapM fun e => do
      let label ← e.getStr?
      if !(AllocSite.all.any fun s => s.info.label == label && s.info.count != .cut) then
        throw s!"alloc_armed: {label} is not a consumed allocation site"
      pure label
    else pure []
  if hasArmed && !hasHidden then throw "alloc_armed: an armed run carries its records"
  let trace : Trace := { id, ops, rlimit, hidden, steer, armRecords, napiBeforePut, allocArmed, pauses, bare, routes }
  if (bare || !routes.isEmpty) && !trace.net then throw "net_fixture: only a network trace has a network fixture"
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
  { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED,
    fCount := refs, fOp := some (.fixture name), fInode := some (.fixture name) }

def initialKernel (rlimit : Nat) (net : Bool := false) (bare : Bool := false) : Kernel :=
  let slot (fd : Nat) : Option FileId :=
    if fd < 3 then some 0 else if fd < 8 then some (fd - 2) else none
  let files : Std.TreeMap FileId File := Std.TreeMap.ofList
    ([(0, fixtureFile "console" 4),   -- fds 0-2 plus init's references
      (1, fixtureFile "kcov" 2)] ++    -- fd 3 plus the coverage mapping
     (List.range 4).map fun i =>
       (i + 2, fixtureFile (if !net then "/dev/null" else
         match i with
         | 0 => "udp-listener-127.0.0.1" | 1 => "udp-listener-::1" | 2 => "udp-sender"
         | _ => "generic-netlink") 1))
  let slots := (List.range NR_OPEN_DEFAULT).toArray
  { task := {
      files := { count := 1, resizeInProgress := false, nextFd := 8,
                 fdt := { maxFds := NR_OPEN_DEFAULT, fd := slots.map slot,
                          openFds := slots.map (· < 8), closeOnExec := slots.map fun _ => false } }
      rlimitNofile := rlimit
      -- the trace child blocks SIGPIPE before the first operation and starts
      -- with no pending signal (P design section 6; the guest side is P1's)
      blocked := sigmask SIGPIPE, pending := 0 }
    files, nextFile := 6, ctxs := {}, nextCtx := 0,
    idaUsed := {},
    -- Environment facts: the system-wide open-file count and limit are not
    -- observed; the guest has few files open, far below any boot-sized limit.
    nrFiles := 6, maxFiles := 1000000, anonInodeInodeErr := false,
    -- Pipes (P design section 5): sysctl defaults, and `root_user`'s
    -- `pipe_bufs` at its baseline of 0 (no pipes outside the trace)
    pipeMaxSize := 1048576, pipeUserPagesSoft := 16384, pipeUserPagesHard := 0, user := { pipeBufs := 0 },
    wg := if net && !bare then some { ifindex := 3, ifname := "wg0" } else none,
    -- L: the netns's ifindex cursor (lo 1, sit0 2, the fixture's wg0 3) and
    -- the ratelimiter's reference count (the fixture's wg0 holds one; every
    -- earlier trace process deleted its devices)
    netIfindexNext := if net && !bare then 4 else 3,
    ratelimiter := { refcnt := if net && !bare then 1 else 0 } }

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
def writeSigpipe (k : Kernel) : Json :=
  toJson (if sigismember k.task.pending SIGPIPE then (1 : Nat) else 0)

def toSyscall (results : Array Int) (ends : Array (Option (Nat × Nat))) (index : Nat) : Operation → Syscall
  | .eventfd2 init flags => .eventfd2 init flags
  | .dup fd => .dup (uint (resolveFD results ends fd))
  | .dup3 fd newfd flags => .dup3 (uint (resolveFD results ends fd)) (uint (resolveFD results ends newfd)) flags
  | .close fd => .close (uint (resolveFD results ends fd))
  | .read fd count => .read (uint (resolveFD results ends fd)) count
  | .write fd count value => .write (uint (resolveFD results ends fd)) count (writeBuffer index value count)
  | .fcntl fd cmd arg => .fcntl (uint (resolveFD results ends fd)) cmd arg.toUInt64
  | .pipe2 flags => .pipe2 flags
  | .wgSet attrs => .wgSet attrs
  | .wgGet => .wgGet
  | .wgUp => .wgUp
  | .wgXmit family addr payload opts => .wgXmit family addr payload opts
  | .wgSetMtu mtu => .wgSetMtu mtu
  | .wgObserve => .wgObserve
  | .wgInject family port message => .wgInject family port message
  | .wgFlood count port messages => .wgFlood count port messages
  | .wgBatch items waitMs => .wgBatch items waitMs
  | .wgAdvance ticks => .wgAdvance ticks
  | .wgCreate => .wgCreate
  | .wgDown => .wgDown
  | .wgDelete => .wgDelete

/-- Run a trace. A `Stop` is returned with the operation index: the mirror
    never reports an observation for a path it does not model. -/
def executeTrace (trace : Trace) (placeholders : Bool := false) : Except (Nat × Stop) Json := do
  let mut world : World := { k := initialKernel trace.rlimit trace.net trace.bare, env := harnessEnv,
                             timing := Env.timing, portBound := Env.portBound,
                             allocArmed := trace.allocArmed, routes := trace.routes,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords,
                             napiBeforePut := trace.napiBeforePut,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    world := { world with hidden := trace.hidden.map (·[index]!), yieldedWorkers := [], pendingStops := [], netRxRaised := false }
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← skipAmbient.run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let s :: _ := w.pendingStops then
      throw (index, .hidden s!"a section stop of site {s} ended in the mirror but has no record")
    if w.netRxRaised then
      throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
    world := w
    results := results.push ret
    ends := ends.push (if ret == 0 then w.userFds else none)
    -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8)
    let bytes := match op, w.userOut with
      | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
      | _, _ => ""
    -- pipe2: the pair copied to the caller, or null on failure; a read's
    -- digest; a write's sigpipe (P design section 6)
    let fds : List (String × Json) := match op with
      | .pipe2 _ => [("fds", match w.userFds with
          | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
          | none => .null)]
      | .read .. => [("digest", readDigest w.userOut ret)]
      | .write .. => [("sigpipe", writeSigpipe w.k)]
      | _ => []
    let device := w.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ fds ++ device))
    for s in w.steps do
      -- W7 stream H: the NET_RX section ordinal of a step inside one
      let fields := [("index", toJson index), ("label", toJson s.label)]
        ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
      branches := branches.push (Json.mkObj (match s.operands, s.excluded with
        | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
        | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
        | none, none => fields))
    for symbol in w.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  -- a placement the check chose must have been met
  if world.napiBeforePut.any id then
    throw (results.size - 1, .invariant "napi_irq_before_put names more NAPI polls than the trace has")
  -- the domain filter: a schedule entry for an allocation site that the
  -- mirror never met would be left over in the kernel
  if world.hiddenPlaceholders && world.steerValues.any (fun e => world.allocSteered.contains e.1) then
    throw (trace.ops.size - 1, .outsideDomain "steer" "allocation schedule entries beyond the encounters")
  -- D3: the timer sections the environment ran (`fired:<symbol>`
  -- expectations), present only when one ran
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.napiAmbiguous)] else []))

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
      ("repeatable", toJson d.repeatable),
      ("comparison", match d.comparison with
        | some c => Json.mkObj [("rel", toJson c.rel.name), ("const_rhs", toJson c.constRhs),
            ("site", match c.site with | some l => toJson s!"{i.file}:{l}" | none => .null),
            ("assigned", toJson c.assigned)]
        | none => .null)]).toArray

end Leanux.Runner
