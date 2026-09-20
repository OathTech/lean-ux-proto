import Leanux.FS.File
import Lean.Data.Json

namespace Leanux.Runner
open Lean FS

inductive FDArg where
  | literal (value : Int)
  | ref (index : Nat)
  deriving Repr

inductive FcntlCmd where
  | getFD | setFD | getFL
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
      return .fcntl fd .getFD arg
    | "F_SETFD" => return .fcntl fd .setFD arg
    | "F_GETFL" =>
      if arg != 0 then throw "getter arg must be zero"
      return .fcntl fd .getFL arg
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

structure Step where
  state : Files
  ret : Int
  bytes : String := ""
  branches : List String := []

private def fail (s : Files) (err : Nat) (labels : List String) : Step :=
  { state := s, ret := -(Int.ofNat err), branches := labels }

private def success (s : Files) (ret : Nat) (labels : List String) : Step :=
  { state := s, ret := Int.ofNat ret, branches := labels }

def resolveFD (results : Array Int) : FDArg → Int
  | .literal n => n
  | .ref i =>
    match results[i]? with
    | some n => if n < 0 then -1 else n
    | none => -1 -- Only reachable when bypassing parseTrace.

/-- All descriptor syscalls convert arguments to unsigned 32-bit FDs. Signed
    literals in this contract can name live slots only when they are nonnegative. -/
private def resolveLive (s : Files) (fd : Int) : Option (Nat × FDEntry × File) := do
  if fd < 8 || fd >= Int.ofNat s.limit then none else do
    let number := fd.toNat
    let entry ← lookupDescriptor s number
    let file ← s.objects entry.objectId
    some (number, entry, file)

private def hexByte (n : Nat) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[n / 16 % 16]!, digits[n % 16]!]

def wordBytes (value : UInt64) : String :=
  String.join ((List.range 8).map fun i => hexByte (value.toNat / 256 ^ i % 256))

def doEventfd (s : Files) (init flags : UInt32) : Step :=
  if flags &&& (~~~ (526337 : UInt32)) != 0 then
    fail s 22 ["do_eventfd.invalid_flags"]
  else
    match allocFd s with
    | none => fail s 24 ["do_eventfd.valid_flags", "alloc_fd.limit"]
    | some (fd, reserved) =>
      let file : File := {
        ctx := { count := UInt64.ofNat init.toNat, semaphore := flags &&& 1 != 0 }
        statusFlags := 2050 }
      let created := updateObject reserved s.nextObject file
      let installed := fdInstall created fd ⟨s.nextObject, flags &&& 524288 != 0⟩
      success { installed with nextObject := s.nextObject + 1 } fd
        ["do_eventfd.valid_flags", "alloc_fd.reserve", "anon_inode_getfile.create", "fd_install"]

def dupFd (s : Files) (fd : Int) : Step :=
  match resolveLive s fd with
  | none => fail s 9 ["dup.bad_fd"]
  | some (_, entry, _) =>
    match allocFd s with
    | none => fail s 24 ["dup.lookup", "alloc_fd.limit"]
    | some (newfd, reserved) =>
      success (fdInstall reserved newfd { entry with cloexec := false }) newfd
        ["dup.lookup", "alloc_fd.reserve", "dup.share_object", "fd_install"]

def dup3Fd (s : Files) (fd newfd : Int) (flags : UInt32) : Step :=
  if flags &&& (~~~ (524288 : UInt32)) != 0 then
    fail s 22 ["ksys_dup3.invalid_flags"]
  else if fd == newfd then
    fail s 22 ["ksys_dup3.equal_fds"]
  else if newfd < 0 || newfd >= Int.ofNat s.limit then
    fail s 9 ["ksys_dup3.target_limit"]
  else
    match resolveLive s fd with
    | none => fail s 9 ["ksys_dup3.bad_source"]
    | some (_, entry, _) =>
      let replacing := (lookupDescriptor s newfd.toNat).isSome
      success (doDup2 s entry newfd.toNat (flags &&& 524288 != 0)) newfd.toNat
        ["ksys_dup3.lookup", if replacing then "do_dup2.replace" else "do_dup2.unused",
          "do_dup2.share_object"]

def closeFd (s : Files) (fd : Int) : Step :=
  if fd < 8 || fd >= Int.ofNat s.limit then fail s 9 ["close.bad_fd"]
  else
    match fileCloseFd s fd.toNat with
    | none => fail s 9 ["close.bad_fd"]
    | some (_, afterClose) => success afterClose 0 ["file_close_fd_locked.remove", "filp_close.release"]

def readFd (s : Files) (fd : Int) (size : Nat) : Step :=
  match resolveLive s fd with
  | none => fail s 9 ["read.bad_fd"]
  | some (_, entry, file) =>
    let checked := Eventfd.eventfdRead file.ctx size
    match checked.result with
    | .error err => fail s err ("read.dispatch" :: checked.branches)
    | .ok result =>
      { state := updateObject s entry.objectId { file with ctx := result.next }
        ret := 8, bytes := wordBytes result.value
        branches := "read.dispatch" :: checked.branches }

def writeFd (s : Files) (fd : Int) (size : Nat) (value : UInt64) : Step :=
  match resolveLive s fd with
  | none => fail s 9 ["write.bad_fd"]
  | some (_, entry, file) =>
    let checked := Eventfd.eventfdWrite file.ctx size value
    match checked.result with
    | .error err => fail s err ("write.dispatch" :: checked.branches)
    | .ok ctx => success (updateObject s entry.objectId { file with ctx }) 8
      ("write.dispatch" :: checked.branches)

def fcntlFd (s : Files) (fd : Int) (cmd : FcntlCmd) (arg : UInt32) : Step :=
  match resolveLive s fd with
  | none => fail s 9 ["fcntl.bad_fd"]
  | some (number, entry, file) =>
    match cmd with
    | .getFD => success s (if entry.cloexec then 1 else 0) ["fcntl.getfd"]
    | .setFD => success (fdInstall s number { entry with cloexec := arg &&& 1 != 0 }) 0
      ["fcntl.setfd"]
    | .getFL => success s file.statusFlags.toNat ["fcntl.getfl"]

def executeOperation (s : Files) (results : Array Int) : Operation → Step
  | .eventfd2 init flags => doEventfd s init flags
  | .dup fd => dupFd s (resolveFD results fd)
  | .dup3 fd newfd flags => dup3Fd s (resolveFD results fd) (resolveFD results newfd) flags
  | .close fd => closeFd s (resolveFD results fd)
  | .read fd count => readFd s (resolveFD results fd) count
  | .write fd count value => writeFd s (resolveFD results fd) count value
  | .fcntl fd cmd arg => fcntlFd s (resolveFD results fd) cmd arg

def executeTrace (trace : Trace) : Json := Id.run do
  let mut state := initialFiles
  let mut results : Array Int := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    let step := executeOperation state results op
    state := step.state
    results := results.push step.ret
    observations := observations.push (Json.mkObj [
      ("index", toJson index), ("ret", toJson step.ret),
      ("errno", if step.ret < 0 then toJson (-step.ret) else .null),
      ("bytes", toJson step.bytes)])
    for label in step.branches do
      branches := branches.push (Json.mkObj [("index", toJson index), ("label", toJson label)])
  return Json.mkObj [("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]

end Leanux.Runner
