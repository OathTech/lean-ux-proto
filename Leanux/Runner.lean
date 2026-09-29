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
  deriving Repr

def Operation.isProducer : Operation → Bool
  | .eventfd2 .. | .dup .. | .dup3 .. => true
  | _ => false

structure Trace where
  id : String
  ops : Array Operation
  deriving Repr

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

private def parseOperation (j : Json) (prior : Array Operation) : Except String Operation := do
  let op ← (← field j "op").getStr?
  match op with
  | "eventfd2" =>
    fields j ["op", "init", "flags"]
    let init ← u32Field j "init"
    let flags ← u32Field j "flags"
    if flags &&& 2048 == 0 then throw "creation must request nonblocking mode"
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
    | "F_GETFD" =>
      if arg != 0 then throw "getter arg must be zero"
      return .fcntl fd FcntlCmd.getFD arg
    | "F_SETFD" => return .fcntl fd FcntlCmd.setFD arg
    | "F_GETFL" =>
      if arg != 0 then throw "getter arg must be zero"
      return .fcntl fd FcntlCmd.getFL arg
    | _ => throw "unsupported fcntl command"
  | _ => throw "unsupported operation"

def parseTrace (j : Json) : Except String Trace := do
  fields j ["version", "id", "ops"]
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
  return ⟨id, ops⟩

/-! ## Harness fixture and trace execution

The guest child (harness/guest.c) runs each trace in a fresh forked process:
descriptors 0-2 are the inherited console (one shared `struct file`), 3 is
KCOV (also memory-mapped), 4-7 are separately opened /dev/null files, and
RLIMIT_NOFILE is 32. The fork gave the child its own files_struct
(`count = 1`) with the embedded 64-slot table. Allocation history leaves
`next_fd = 8`. Fixture files carry references held outside the trace. -/

def fixtureFile (name : String) (refs : Nat) : File :=
  { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED,
    fCount := refs, kind := .fixture name }

def initialKernel : Kernel :=
  let slot (fd : Nat) : Option FileId :=
    if fd < 3 then some 0 else if fd < 8 then some (fd - 2) else none
  let files : Nat → Option File := fun
    | 0 => some (fixtureFile "console" 4)   -- fds 0-2 plus init's references
    | 1 => some (fixtureFile "kcov" 2)      -- fd 3 plus the coverage mapping
    | n@(_ + 2) => if n < 6 then some (fixtureFile "/dev/null" 1) else none
  { task := {
      files := { count := 1, resizeInProgress := false, nextFd := 8,
                 fdt := { maxFds := NR_OPEN_DEFAULT, fd := slot,
                          openFds := fun fd => fd < 8, closeOnExec := fun _ => false } }
      rlimitNofile := 32 }
    files, nextFile := 6, ctxs := fun _ => none, nextCtx := 0,
    idaUsed := fun _ => false,
    -- Environment facts: the system-wide open-file count and limit are not
    -- observed; the guest has few files open, far below any boot-sized limit.
    nrFiles := 6, maxFiles := 1000000, anonInodeInodeErr := false }

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

/-- Run a trace. An `unsupported` outcome is returned as an error: the mirror
    never reports an observation for a path it does not model. -/
def executeTrace (trace : Trace) : Except String Json := do
  let mut world : World := { k := initialKernel, env := harnessEnv }
  let mut results : Array Int := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    let (ret, w) ← (syscall (toSyscall results op)).run world
      |>.mapError fun e => s!"trace {trace.id} operation {index}: {e}"
    world := w
    results := results.push ret
    let bytes := match op, w.userOut with
      | .read .., some v => if ret == 8 then wordBytes v else ""
      | _, _ => ""
    observations := observations.push (Json.mkObj [
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)])
    for s in w.steps do
      branches := branches.push (Json.mkObj [("index", toJson index), ("label", toJson s.label)])
  return Json.mkObj [("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]

def spanJson (s : Span) : Json :=
  Json.mkObj [("file", toJson s.file), ("lo", toJson s.lo), ("hi", toJson s.hi)]

/-- The decision table, for the check's KCOV comparison. -/
def decisionsJson : Json :=
  .arr (Decision.all.map fun d =>
    let i := d.info
    Json.mkObj [("label", toJson i.label), ("file", toJson i.file), ("line", toJson i.line),
      ("when_true", .arr (i.whenTrue.map spanJson).toArray),
      ("when_false", .arr (i.whenFalse.map spanJson).toArray),
      ("unobservable_true", match d.unobservable true with | some r => toJson r.name | none => .null),
      ("unobservable_false", match d.unobservable false with | some r => toJson r.name | none => .null)]).toArray

end Leanux.Runner
