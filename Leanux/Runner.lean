import Leanux.Syscalls
import Lean.Data.Json

namespace Leanux.Runner
open Lean Leanux

inductive FDArg where
  | literal (value : Int)
  | ref (index : Nat)
  deriving Repr

inductive Operation where
  | eventfd2 (init flags : UInt32)
  | dup (fd : FDArg)
  | dup3 (fd newfd : FDArg) (flags : UInt32)
  | close (fd : FDArg)
  | read (fd : FDArg) (count : Nat)
  | write (fd : FDArg) (count : Nat) (value : UInt64)
  | fcntl (fd : FDArg) (cmd : FcntlCmd) (arg : UInt32)
  | wgSet (attrs : WG.DeviceAttrs)
  | wgGet
  | wgUp
  | wgXmit (family addr : Nat) (payload : List UInt8)
  | wgObserve
  | wgInject (family port : Nat) (message : List UInt8)
  /-- D3: the virtual time advance (harness/trace.py `wg_advance`). -/
  | wgAdvance (ticks : Nat)
  deriving Repr

def Operation.isProducer : Operation → Bool
  | .eventfd2 .. | .dup .. | .dup3 .. => true
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
  deriving Repr

/-- The network fixture runs for traces with a WireGuard operation
    (harness/trace.py `uses_wireguard`). -/
def Trace.net (t : Trace) : Bool :=
  t.ops.any fun
    | .wgSet _ | .wgGet | .wgUp | .wgXmit .. | .wgObserve | .wgInject .. | .wgAdvance _ => true
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
    return .read (← parseFD (← field j "fd") prior) (← natField j "count" 16)
  | "write" =>
    fields j ["op", "fd", "count", "value"]
    return .write (← parseFD (← field j "fd") prior) (← natField j "count" 16)
      (← parseValue j)
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
  | "wg_advance" =>
    fields j ["op", "ticks"]
    let ticks ← natField j "ticks" (2 ^ 31)
    if ticks == 0 then throw "ticks: expected 1-2^31"
    return .wgAdvance ticks
  | "wg_xmit" =>
    fields j ["op", "packet"]
    let p ← field j "packet"
    -- the UDP payload (D2); without one, the fixture's historic 4 bytes "leux"
    let payload ← match p.getObjVal? "payload" with
      | .ok v => do
        fields p ["family", "dst", "payload"]
        let s ← v.getStr?
        if s.length == 0 || s.length % 2 != 0 || s.length > 2 * 1392 then
          throw "packet.payload: expected 1-1392 bytes of lowercase hex"
        hexBytes v s.length "packet.payload"
      | .error _ => do
        fields p ["family", "dst"]
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
    return .wgXmit family addr payload
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
  fields j ((if hasLimit then ["version", "id", "ops", "rlimit_nofile"] else ["version", "id", "ops"])
    ++ (if hasHidden then ["hidden"] else []) ++ (if hasSteer then ["steer"] else [])
    ++ (if hasExpect then ["expect"] else []) ++ (if hasArm then ["arm_records"] else []))
  -- D3: the arm-record switch qualifies the records, so it comes with them
  if hasArm && !hasHidden then throw "arm_records: only with hidden records"
  let armRecords ← if hasArm then (← field j "arm_records").getBool? else pure false
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
  for j in rawOps do
    ops := ops.push (← parseOperation j ops)
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
  return { id, ops, rlimit, hidden, steer, armRecords }

/-! ## Harness fixture and trace execution

The guest child (harness/guest.c) runs each trace in a fresh forked process:
descriptors 0-2 are the inherited console (one shared `struct file`), 3 is
KCOV (also memory-mapped), 4-7 are separately opened /dev/null files, and
RLIMIT_NOFILE is 32. The fork gave the child its own files_struct
(`count = 1`) with the embedded 64-slot table. Allocation history leaves
`next_fd = 8`. Fixture files carry references held outside the trace.

The network fixture (traces with a WireGuard operation) runs in a new network
namespace holding `lo` (up) and a down WireGuard device `wg0` at ifindex 3.
Descriptors 4 and 5 are UDP listeners on 127.0.0.1 and ::1 at `LISTEN_PORT`,
6 a dual-stack UDP sender, and 7 a generic-netlink socket, instead of
/dev/null. -/

/-- A fixture file. Its mode, operations and inode are outside the slice: any
    operation that consults them is `unsupported`. -/
def fixtureFile (name : String) (refs : Nat) : File :=
  { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED,
    fCount := refs, fOp := some (.fixture name), fInode := some (.fixture name) }

def initialKernel (rlimit : Nat) (net : Bool := false) : Kernel :=
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
      rlimitNofile := rlimit }
    files, nextFile := 6, ctxs := {}, nextCtx := 0,
    idaUsed := {},
    -- Environment facts: the system-wide open-file count and limit are not
    -- observed; the guest has few files open, far below any boot-sized limit.
    nrFiles := 6, maxFiles := 1000000, anonInodeInodeErr := false,
    wg := if net then some { ifindex := 3, ifname := "wg0" } else none }

/-- The harness environment: every allocation and user-memory access succeeds. -/
def harnessEnv : EnvSite → Nat → Bool := fun _ _ => true

def resolveFD (results : Array Int) : FDArg → Int
  | .literal n => n
  | .ref i =>
    match results[i]? with
    | some n => if n < 0 then -1 else n
    | none => -1 -- Only reachable when bypassing parseTrace.

private def hexByte (n : Nat) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[n / 16 % 16]!, digits[n % 16]!]

def wordBytes (value : UInt64) : String :=
  String.join ((List.range 8).map fun i => hexByte (value.toNat / 256 ^ i % 256))

def toSyscall (results : Array Int) : Operation → Syscall
  | .eventfd2 init flags => .eventfd2 init flags
  | .dup fd => .dup (uint (resolveFD results fd))
  | .dup3 fd newfd flags => .dup3 (uint (resolveFD results fd)) (uint (resolveFD results newfd)) flags
  | .close fd => .close (uint (resolveFD results fd))
  | .read fd count => .read (uint (resolveFD results fd)) count
  | .write fd count value => .write (uint (resolveFD results fd)) count value
  | .fcntl fd cmd arg => .fcntl (uint (resolveFD results fd)) cmd arg.toUInt64
  | .wgSet attrs => .wgSet attrs
  | .wgGet => .wgGet
  | .wgUp => .wgUp
  | .wgXmit family addr payload => .wgXmit family addr payload
  | .wgObserve => .wgObserve
  | .wgInject family port message => .wgInject family port message
  | .wgAdvance ticks => .wgAdvance ticks

/-- Run a trace. A `Stop` is returned with the operation index: the mirror
    never reports an observation for a path it does not model. -/
def executeTrace (trace : Trace) (placeholders : Bool := false) : Except (Nat × Stop) Json := do
  let mut world : World := { k := initialKernel trace.rlimit trace.net, env := harnessEnv, timing := Env.timing,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords }
  let mut results : Array Int := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    world := { world with hidden := trace.hidden.map (·[index]!), yieldedWorkers := [], pendingStops := [] }
    let (ret, w) ← (syscall (toSyscall results op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← skipAmbient.run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let s :: _ := w.pendingStops then
      throw (index, .hidden s!"a section stop of site {s} ended in the mirror but has no record")
    world := w
    results := results.push ret
    let bytes := match op, w.userOut with
      | .read .., some v => if ret == 8 then wordBytes v else ""
      | _, _ => ""
    let device := w.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ device))
    for s in w.steps do
      let fields := [("index", toJson index), ("label", toJson s.label)]
      branches := branches.push (Json.mkObj (match s.operands with
        | some (a, b) => fields ++ [("operands", toJson [a, b])]
        | none => fields))
    for symbol in w.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  -- D3: the timer sections the environment ran (`fired:<symbol>`
  -- expectations), present only when one ran
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)]))

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
