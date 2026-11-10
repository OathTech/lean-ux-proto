import StatementC1Vacuity
import C1Step
import PairCapture
import PairAllowedipsCapture

/-! C1 phase A: the statements' own executable definitions evaluated on
states captured from a booted s5 guest (`capture_insertions.py`, slimmed by
`analyse.py`). Not a proof and not part of the package build; run with
`run-capture.sh`.

Per captured call of a wrapper: `insertReady` (and `emptyTable` at the first
call) on the captured entry state; the mirror's `Leanux.WG.insert` on the
same arguments from the threaded world; then Kraken executes the compiled
wrapper, `add`, `common_bits` and the coverage callbacks from the captured
entry state. At each stop at a service address the interpreter's state is
compared with the captured one, the clause's hypotheses and `ServiceReady`
(with revision 3's separation) are evaluated, the captured return state is installed (the service is
executed by the guest, not interpreted), and every byte of the captured
blocks that changed is judged against `ServiceWrites` with `Kept`. At the
end the interpreter's final state is compared with the captured return
state, and `Returned`, `eax`, `SeqAdvanced`, the write frame and the landed
relation are checked. Between two calls the heap bytes the caller changed
are read as steps of the closed world (`referenceMoves`: revision 3's
`Referenced`). Nothing is repaired: every failed check is reported
under its name and the run continues where it can. -/
namespace Binary.Statements.C1.CaptureCheck
open Lean Leanux Leanux.WG Binary Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1
open Binary.Pair.Capture (loadMemory compareEndpoint)
abbrev Endpoint := Binary.Pair.Capture.Endpoint

structure ServiceIn where
  kind : String
  initial : Endpoint
  returned : Endpoint
  allocation : Nat
  deriving FromJson

structure CallIn where
  family : Nat
  key : Nat
  cidr : Nat
  pid : Nat
  initial : Endpoint
  returned : Endpoint
  services : Array ServiceIn
  executedPCs : Array Nat
  deriving FromJson

structure CaptureIn where
  table : Nat
  peers : Array Nat
  arena : Array (Nat × Nat)
  cache : Nat
  depth : Nat
  calls : Array CallIn
  lookups : Array (Nat × Nat)
  deriving FromJson

def inside (a n : Nat) (spans : List Pair.Span) : Bool := spans.any fun (b,k) => b ≤ a && a+n ≤ b+k

def returned (s t : MachineState) (ra : Nat) : Bool :=
  t.pc.toBitVec.toNat == ra && t.data.regs.rsp == s.data.regs.rsp+8 &&
  [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15].all fun reg => t.data.regs.get64 reg == s.data.regs.get64 reg

def say (e : Except String Unit) : String := match e with | .ok _ => "ok" | .error m => m
def check (ok : Bool) : String := if ok then "ok" else "FAILS"

def world (peers : Nat) : World :=
  let peers := (List.range peers).foldl (fun peers id => peers.insert id {
    remoteStatic := List.replicate 32 0,presharedKey := List.replicate 32 0,
    precomputedStaticStatic := List.replicate 32 0,internalId := id})
    ({} : Std.TreeMap PeerId Peer)
  let dev : Device := {ifindex := 1,ifname := "wg0",peers}
  let ambient : Ambient := {
    env := Runner.harnessEnv,timing := Env.timing,hidden := some [],
    allocArmed := ["allocNode190","allocNode205","allocNode234"]}
  {ambient,tasks := Runner.initialTasks 1024 false false false,fs := {},wg := {dev := some dev}}

/-- `CountMoved` (revision 3) on captured memories: both counts readable with
the stated values, and every other heap byte the same. A byte captured in
neither memory compares equal; the whole-RAM comparison of the same gap is
`analyse.py`'s (`between`). -/
def countMoved (L : Layout) (pid before after : Nat) (m m' : DataMem) : Except String Unit := do
  let peer ← Trie.address L.peers (some pid)
  let word := peer+Root.nodeOffsets.peerRefcount
  require ((← readNat ⟨{dmem := m},0⟩ word 4) == before) s!"the count before is not {before}"
  require ((← readNat ⟨{dmem := m'},0⟩ word 4) == after) s!"the count after is not {after}"
  for (a,n) in L.heap do
    for i in [:n] do
      unless word ≤ a+i && a+i < word+4 do
        unless m.get? (.ofNat 64 (a+i)) == m'.get? (.ofNat 64 (a+i)) do
          throw s!"heap byte {a+i} differs"

/-- What the caller did to the heap since the last call, read as steps of the
closed world. Revision 2 admits none (`Framed`: no heap byte changes).
Revision 3 also admits `Referenced`: one peer's count word up by one with
the mirror's `peerGetMaybeZero` returning the peer, or down by one from above one with the mirror's
`peerPut`. The steps are found from the two counts (drops first, as
`set_peer` drops its reference before the next one is taken), each is run
on the mirror and on an intermediate memory and judged by `countMoved`, and
the memory after the last step must agree with the captured entry state on
every heap byte. Returns the mirror's world after the steps, the steps, and
whether the gap is inside revision 2's and revision 3's closed world. -/
def referenceMoves (L : Layout) (previous : DataMem) (entry : MachineState) (w : World) :
    Except String (World × List String × Bool × String) := do
  let mut w := w
  let mut m := previous
  let mut notes : List String := []
  let mut steps : List (Nat × Bool) := []
  for drop in [true,false] do
    for (pid,a) in L.peers do
      let before ← readNat ⟨{dmem := previous},0⟩ (a+Root.nodeOffsets.peerRefcount) 4
      let after ← readNat entry (a+Root.nodeOffsets.peerRefcount) 4
      if drop && after < before then steps := steps ++ List.replicate (before-after) (pid,true)
      if !drop && before < after then steps := steps ++ List.replicate (after-before) (pid,false)
  for (pid,drop) in steps do
    let peer ← Trie.address L.peers (some pid)
    let count ← readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4
    let next := if drop then count-1 else count+1
    let name := if drop then "peerPut" else "peerGetMaybeZero"
    if drop && !(1 < count) then
      return (w,notes ++ [s!"{name} {pid}: {count} -> {next} REFUSED: the last reference"],false,"FAILS: a count dropped to zero")
    let step : Except Stop (Bool × World) := if drop then ((liftWG (WG.peerPut (some pid))).run w).map fun (_,w') => (true,w')
      else ((liftWG (WG.peerGetMaybeZero (some pid))).run w).map fun (got,w') => (got == some pid,w')
    match step with
    | .error e => return (w,notes ++ [s!"{name} {pid}: MIRROR refuses: {Stop.message e}"],false,"FAILS: the mirror refuses the step")
    | .ok (false,_) => return (w,notes ++ [s!"{name} {pid}: the mirror returns no peer"],false,"FAILS: the mirror takes no reference")
    | .ok (true,w') =>
      let m' := put m (peer+Root.nodeOffsets.peerRefcount) 4 next
      match countMoved L pid count next m m' with
      | .error e => return (w,notes ++ [s!"{name} {pid}: {e}"],false,s!"FAILS: {e}")
      | .ok _ => notes := notes ++ [s!"{name} {pid}: {count} -> {next} ok"]; w := w'; m := m'
  -- what is left after the steps must be `Framed`'s: no heap byte differs
  let mut stray : List String := []
  for (a,n) in L.heap do
    for i in [:n] do
      unless m.get? (.ofNat 64 (a+i)) == entry.data.dmem.get? (.ofNat 64 (a+i)) do
        if stray.length < 8 then stray := stray ++ [s!"{a+i}"]
  let third := if stray.isEmpty then "ok" else s!"FAILS: heap bytes changed besides the paired counts, at {stray}"
  return (w,notes,steps.isEmpty && stray.isEmpty,third)

structure Thread where
  world : World
  names : Allowedips.Names
  live : List Nat := []
  /-- The heap as the last call left it; none before the first call. -/
  previous : Option DataMem := none
  /-- Every gap so far was inside the closed world of revision 2 / revision 3. -/
  closed2 : Bool := true
  closed3 : Bool := true

/-- The guest's coverage buffer is 32 MiB and `Context.At` asks that every
word of it be readable. Only the words a call can reach are captured, so
the readiness checks are evaluated on a view of the state whose buffer ends
where the captured words end: the capacity word and the context's capacity
are reduced to that number, nothing else. `fullEntry` evaluates the same
definitions on the whole buffer at the first call. -/
def truncated (m : DataMem) (c : CommonBitsCoverage.Context) : DataMem × CommonBitsCoverage.Context × Nat :=
  if decide c.Needed then
    let words := ((List.range 65536).takeWhile fun i =>
      (m.loadInt (c.coverage.area + .ofNat 64 (8*i)) 8).isSome).length
    (put m (c.coverage.task+0x6e4).toNat 4 words,⟨{c.coverage with capacity := .ofNat 32 words},c.preempt⟩,words)
  else (m,c,0)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- One captured service transition against the clause it falls under. -/
def serviceStep (L : Layout) (A : Allocator) (svc : ServiceIn) (entry : MachineState) (live : List Nat)
    (pending : List HiddenRecord) : Except String (MachineState × List Nat × List HiddenRecord × Json) := do
  let mut out : List (String × Json) := [("kind",toJson svc.kind)]
  let note (out : List (String × Json)) (k v : String) := out ++ [(k,toJson v)]
  let rsp := entry.data.regs.rsp.toNat
  let ra ← readNat entry rsp 8
  let c ← Common.readContext entry.data.dmem
  let isAlloc := entry.pc == allocEntry
  out := note out "interpreter state equals the captured entry state" (match compareEndpoint svc.initial entry with
    | .ok n => s!"ok ({n} bytes)" | .error e => e)
  out := note out "pc is the service address" (check ((isAlloc && svc.kind == "alloc") || (entry.pc == freeEntry && svc.kind == "free")))
  out := note out "EntryFrame (rsp aligned, return word)" (check (rsp % 8 == 0))
  let (viewMemory,view,_) := truncated entry.data.dmem c
  out := note out "ServiceReady.coverage (captured window)" (check (Trie.coverageCheck view viewMemory))
  out := note out "ServiceReady.capacity" (check (if c.Needed then 0 < c.coverage.capacity.toNat else true))
  out := note out "ServiceReady.forward" (check (entry.data.system.bits[10] == false))
  out := note out "ServiceReady.stackMapped" (check ((List.range A.depth).all fun i =>
    (entry.data.dmem.get? (.ofNat 64 (rsp-A.depth+i))).isSome))
  -- `ServiceReady.separated` (revision 3) on the spans that cover its byte sets; the whole buffer, no window
  let stack := [(rsp-A.depth,A.depth+8)]
  out := note out "ServiceReady.separated: stack (scratch, return word) apart from the arena" (check (spansApart stack L.arena))
  out := note out "ServiceReady.separated: stack apart from the coverage bytes" (check (spansApart stack (Trie.readSpans c)))
  out := note out "ServiceReady.separated: coverage bytes apart from the arena" (check (spansApart (Trie.readSpans c) L.arena))
  out := note out "ServiceReady.separated: buffer apart from the coverage metadata and the preemption count" (check (
    spansApart (Trie.writeSpans c) (Trie.metadataSpans c ++ [(preemptCountAddress.toNat,4)])))
  out := note out "rdi is the cache" (check (entry.data.regs.rdi.toNat == L.cache))
  let record := pending.head?
  if isAlloc then
    out := note out "esi is 0xdc0" (check (entry.data.regs.get (.low .rsi .W32) == 0xdc0#32))
    out := note out "return site against the mirror's pending record" (match record with
      | none => "FAILS: the mirror has no pending record"
      | some r => if allocSites.contains (ra,r.site) then s!"ok (site {r.site})"
          else s!"FAILS: return address {hex ra}, pending record site {r.site}")
  else
    out := note out "free: return site and rsi handed out" (check (ra == freeSite && live.contains entry.data.regs.rsi.toNat))
  -- install the captured return state; judge every changed captured byte
  let kept := if isAlloc then live else live.erase entry.data.regs.rsi.toNat
  let mut memory := entry.data.dmem
  let mut outside : List String := []
  let mut changed := 0
  for block in svc.returned.blocks do
    for i in [:block.bytes.size] do
      let a := block.address+i
      let byte := block.bytes[i]!.toUInt8
      if memory.get? (.ofNat 64 a) != some byte then
        changed := changed+1
        let scratch := inside a 1 [(rsp-A.depth,A.depth)]
        let buffer := inside a 1 (Trie.writeSpans c)
        let arena := inside a 1 L.arena && kept.all fun object => disjointRanges a 1 object nodeSize
        unless scratch || buffer || arena do
          if outside.length < 24 then outside := outside ++ [hex a]
        memory := memory.insert (.ofNat 64 a) byte
  let t ← svc.returned.registers.state memory
  out := note out "Returned" (check (returned entry t ra))
  out := out ++ [("captured bytes changed",toJson changed)]
  out := note out "EqualOutside ServiceWrites (captured blocks)" (if outside.isEmpty then "ok" else s!"FAILS at {outside}")
  out := note out "c.At afterwards (captured window)" (check (Trie.coverageCheck view (truncated t.data.dmem c).1))
  let mut live := live
  let mut rest := pending
  if isAlloc then
    let a := t.data.regs.rax.toNat
    rest := pending.drop 1
    let byte := record.bind (·.bytes.head?)
    let result := match byte with
      | some 0 => if a == 0 then "ok (NULL, record byte 0)" else s!"FAILS: record byte 0, rax {hex a}"
      | some 1 =>
        let zero := match readNat t a nodeSize with | .ok 0 => true | _ => false
        if a != 0 && a % 8 == 0 && a + nodeSize < 2^64 && inside a nodeSize L.arena &&
            live.all (fun other => disjointRanges a nodeSize other nodeSize) && zero
          then "ok (object, record byte 1)"
          else s!"FAILS: record byte 1, rax {hex a}, aligned {a % 8 == 0}, below 2^64 {decide (a + nodeSize < 2^64)}, in arena {inside a nodeSize L.arena}, zero {zero}"
      | _ => s!"no usable record; rax {hex a}"
    out := note out "AllocResult against the mirror's pending record" result
    if a != 0 then live := live ++ [a]
  else live := kept
  return (t,live,rest,Json.mkObj out)

def insertCall (L : Layout) (A : Allocator) (input : Input) (seed : UInt64) (th : Thread)
    (index : Nat) (call : CallIn) : Except String (Thread × MachineState × Json) := do
  let mut out : List (String × Json) := [("call",toJson index),("family",toJson call.family),
    ("key",toJson (hex call.key)),("cidr",toJson call.cidr),("pid",toJson call.pid)]
  let note (out : List (String × Json)) (k v : String) := out ++ [(k,toJson v)]
  let memory ← loadMemory call.initial.blocks
  let initial ← call.initial.registers.state memory
  let ra ← readNat initial initial.data.regs.rsp.toNat 8
  let c ← Common.readContext initial.data.dmem
  -- the gap since the last call, as steps of the closed world
  let (w,notes,second,third) ← match th.previous with
    | none => pure (th.world,[],true,"ok")
    | some previous => referenceMoves L previous initial th.world
  let closed2 := th.closed2 && second
  let closed3 := th.closed3 && third == "ok"
  out := out ++ [("reference moves by the caller since the last call (Referenced)",toJson notes)]
  out := out ++ [("gap since the last call: inside revision 2's closed world (no heap byte changed)",toJson second)]
  out := note out "gap since the last call: inside revision 3's closed world (paired reference moves only)" third
  out := out ++ [("covered by the headline from the empty table, revision 2",toJson closed2),
    ("covered by the headline from the empty table, revision 3",toJson closed3)]
  unless third == "ok" do
    throw s!"outside the closed world of revision 3 before call {index}: {third} {notes}"
  if index == 0 then
    let some d := w.wg.dev | throw "no device"
    out := note out "emptyTable" (say (emptyTable L memory d))
    out := note out "proof plan's invariant at the empty table (Initial; C1Invariant.relatedCheck)" (say (
      Proof.relatedCheck L ⟨L.table,⟨[],L.peers⟩,d.nextNode⟩ w memory))
  let (viewMemory,view,words) := truncated memory c
  out := note out "insertReady (captured window)" (say (insertReady L A view
    {initial with data := {initial.data with dmem := viewMemory}} call.family call.key call.cidr call.pid (.ofNat ra)))
  out := note out "c1.stack-peers (revision 4): the stack window apart from every peer object" (check (
    spansApart [((initial.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow+A.depth)).toNat,insertWindow+A.depth)]
      (L.peers.map fun (_,a) => (a,Layouts.peerSize))))
  let own := callerSpans initial (insertWindow+A.depth) (initial.data.regs.rsi.toNat,if call.family == 4 then 4 else 16) true
  out := note out "whole buffer apart from the heap, the caller's spans and the coverage metadata" (check (
    spansApart (Trie.callBuffers c) (L.heap ++ own ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)])))
  out := out ++ [("captured buffer words",toJson words)]
  out := out ++ [("coverage mode",toJson c.coverage.mode.toNat),("preempt count",toJson c.preempt.toNat),
    ("coverage capacity (words)",toJson c.coverage.capacity.toNat)]
  let some stream := w.ambient.hidden | throw "no pending records"
  let (answer,w') ← ((liftWG (WG.insert call.family call.key call.cidr call.pid)).run w).mapError
    (s!"MIRROR refuses: {Stop.message ·}")
  out := out ++ [("mirror answer",toJson answer)]
  let mut r : Run := {state := initial}
  let mut live := th.live
  let mut names := th.names
  let mut pending := stream
  let mut services : Array Json := #[]
  for k in [:4] do
    r ← (runUntil input.lookup.instructions input.lookup.labels input.lookup.hooks input.lookup.preempt
      r.state seed true 200000 c.preempt.toNat #[input.alloc,input.free] (some r) ra (some #[])).mapError
      (s!"the interpreter does not reach the next stop: {·}")
    if r.state.pc.toBitVec.toNat == ra then break
    let some svc := call.services[k]? | throw "the interpreter calls a service the guest did not"
    let entry := r.state
    let (t,live',rest,report) ← serviceStep L A svc entry live pending
    if entry.pc == allocEntry then
      if t.data.regs.rax.toNat != 0 then names := names.allocated t.data.regs.rax.toNat
    else names := {names with trie := {names.trie with
      nodes := names.trie.nodes.filter (·.2 != entry.data.regs.rsi.toNat)}}
    r := {r with state := t}; live := live'; pending := rest
    services := services.push report
  let t := r.state
  out := out ++ [("services",Json.arr services)]
  out := note out "service calls: interpreter and guest agree on the number" (check (services.size == call.services.size))
  out := note out "instruction addresses: interpreter equals guest" (check (r.pcs == call.executedPCs))
  out := note out "interpreter final state equals the captured return state" (match compareEndpoint call.returned t with
    | .ok n => s!"ok ({n} bytes)" | .error e => e)
  out := note out "Returned" (check (returned initial t ra))
  out := note out "eax is the mirror's answer" (if t.data.regs.get (.low .rax .W32) == BitVec.ofInt 32 answer then "ok"
    else s!"FAILS: eax {t.data.regs.get (.low .rax .W32)}, mirror {answer}")
  let seq := L.table+AllowedipsMutationLayout.seq
  out := note out "SeqAdvanced" (check ((← readNat t seq 8) == ((← readNat initial seq 8)+1) % 2^64))
  let window := insertWindow+A.depth
  let frame := [(initial.data.regs.rsp.toNat-window,window)] ++ Trie.writeSpans c ++ L.heap
  let stray := r.writes.toList.filter fun (a,n) => !inside a n frame
  out := note out "EqualOutside InsertWrites (interpreter's stores)" (if stray.isEmpty then "ok"
    else s!"FAILS at {stray.take 8 |>.map fun (a,n) => (hex a,n)}")
  let deepest := r.writes.foldl (fun low (a,_) =>
    if initial.data.regs.rsp.toNat-4096 ≤ a && a < initial.data.regs.rsp.toNat then min low a else low) initial.data.regs.rsp.toNat
  out := out ++ [("deepest stack write of the six functions and callbacks",toJson (initial.data.regs.rsp.toNat-deepest))]
  out := note out "mirror's pending records after the call are the unconsumed ones" (check (w'.ambient.hidden == some pending))
  out := note out "landed relation (assertAt) after the call" (say (assertAt names Root.nodeOffsets t.data.dmem w'))
  out := note out "proof plan's invariant after the call (C1Invariant.invCheck)" (say (Proof.invCheck L names w' t.data.dmem))
  out := note out "proof plan's walk facts before the call (C1Invariant.walkCheck)" (say (Proof.walkCheck w call.family call.key call.cidr))
  out := note out "proof plan's step equals the mirror's run (C1Step.stepCheck)" (match Proof.stepCheck w call.family call.key call.cidr call.pid answer w' with
    | .ok k => s!"ok ({repr k})" | .error e => e)
  return ({world := w',names,live,previous := some t.data.dmem,closed2,closed3},t,Json.mkObj out)

/-- A compiled lookup under Kraken on the captured heap, with a caller frame
constructed inside the captured stack block (the caller's side is not
captured: `Framed` lets it be anything). -/
def lookupCall (L : Layout) (input : Input) (seed : UInt64) (final : MachineState) (w : World)
    (family key : Nat) : Except String (World × Json) := do
  let some d := w.wg.dev | throw "no device"
  let width := if family == 4 then 32 else 128
  let slot := L.table+(if family == 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6)
  let stack := final.data.regs.rsp.toNat-512
  let keyAt := stack+16
  let memory := (put final.data.dmem stack 8 stopAddr).storeBytes (.ofNat 64 keyAt)
    ((List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256))
  let regs : Reg64s := {final.data.regs with
    rdi := .ofNat (← readNat ⟨{dmem := memory},0⟩ slot 8),rsi := .ofNat width,rdx := .ofNat keyAt,rsp := .ofNat stack}
  let initial : MachineState := ⟨{final.data with regs,dmem := memory},.ofNat input.lookup.entry⟩
  let c ← Common.readContext initial.data.dmem
  let (viewMemory,view,_) := truncated initial.data.dmem c
  let ready := say (lookupReady L view {initial with data := {initial.data with dmem := viewMemory}} family key (.ofNat stopAddr))
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let (answer,w') ← ((Source.lookup root width key).run w).mapError (s!"MIRROR refuses: {Stop.message ·}")
  let pointer ← Trie.address L.peers answer
  let r ← (runUntil input.lookup.instructions input.lookup.labels input.lookup.hooks input.lookup.preempt
    initial seed true 200000 c.preempt.toNat #[] none stopAddr (some #[])).mapError (s!"the interpreter does not return: {·}")
  let t := r.state
  return (w',Json.mkObj [("family",toJson family),("key",toJson (hex key)),("lookupReady (captured window)",toJson ready),
    ("Returned",toJson (check (returned initial t stopAddr))),
    ("rax",toJson (hex t.data.regs.rax.toNat)),("mirror",toJson (hex pointer)),
    ("rax is the mirror's peer",toJson (check (t.data.regs.rax.toNat == pointer)))])

end Binary.Statements.C1.CaptureCheck

open Lean Leanux Leanux.WG Binary Binary.Pair Binary.Pair.Allowedips Binary.Statements.C1 Binary.Statements.C1.CaptureCheck in
def main (args : List String) : IO UInt32 := do
  let inputPath :: capturePath :: rest := args | IO.eprintln "usage: Check INPUT.json LEAN-INPUT.json [COVERAGE.bin]"; return 1
  let input ← liftE (Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := Input))
  let cap ← liftE (Json.parse (← IO.FS.readFile capturePath) >>= fromJson? (α := CaptureIn))
  unless input.alloc == allocEntry.toBitVec.toNat && input.free == freeEntry.toBitVec.toNat &&
      input.cacheWord == cacheWord && input.freeReturn == freeSite do
    IO.eprintln "FAIL: statement addresses differ from the ELF-derived input"; return 1
  let L : Binary.Statements.C1.Layout := ⟨cap.table,cap.peers.toList.zipIdx.map (fun (a,i) => (i,a)),cap.arena.toList,cap.cache⟩
  let A : Allocator := ⟨fun _ _ _ => True,cap.depth⟩
  let hidden ← liftE (Json.parse (← IO.FS.readFile capturePath) >>= (·.getObjValAs? (Array (Nat × Array Nat)) "records"))
  let stream : List HiddenRecord := hidden.toList.map fun (site,bytes) => ⟨site,bytes.toList.map (·.toUInt8)⟩
  let w0 := world cap.peers.size
  let w0 := {w0 with ambient := {w0.ambient with hidden := some stream}}
  -- the caller holds a reference on the peer it configures (`set_peer`)
  let w0 ← match cap.calls[0]? with
    | some call => liftE (((liftWG (WG.peerGet call.pid)).run w0).map (·.2) |>.mapError Stop.message)
    | none => pure w0
  if let [bulk] := rest then
    -- the statement's own premises, verbatim, on the first entry state with the whole buffer loaded
    let some call := cap.calls[0]? | return 1
    let bytes ← IO.FS.readBinFile bulk
    let memory ← liftE (Binary.Pair.Capture.loadMemory call.initial.blocks)
    let c ← liftE (Common.readContext memory)
    let memory ← liftE (Binary.Pair.Trie.Capture.loadBulk memory #[(c.coverage.area.toNat,bytes)])
    let initial ← liftE (call.initial.registers.state memory)
    let ra ← liftE (readNat initial initial.data.regs.rsp.toNat 8)
    let some d := w0.wg.dev | return 1
    IO.println (Json.mkObj [("fullEntry",Json.mkObj [
      ("buffer bytes loaded",toJson bytes.size),("capacity (words)",toJson c.coverage.capacity.toNat),
      ("emptyTable",toJson (say (emptyTable L memory d))),
      ("insertReady",toJson (say (insertReady L A c initial call.family call.key call.cidr call.pid (.ofNat ra))))])]).compress
    return 0
  let mut th : CaptureCheck.Thread := {world := w0,names := ⟨L.table,⟨[],L.peers⟩,0⟩}
  let mut final : Option MachineState := none
  for (call,index) in cap.calls.toList.zipIdx do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      match insertCall L A input seed th index call with
      | .ok (next,t,report) =>
        IO.println (Json.mkObj [("seed",toJson seed.toNat),("insertion",report)]).compress
        if seed != 0 then th := next; final := some t
      | .error e =>
        IO.println (Json.mkObj [("seed",toJson seed.toNat),("insertion",Json.mkObj [("call",toJson index),("ABORTED",toJson e)])]).compress
        if seed != 0 then return 1
    (← IO.getStdout).flush
  if let some t := final then
    let mut w := th.world
    for (family,key) in cap.lookups do
      match lookupCall L input 0 t w family key with
      | .ok (w',report) => w := w'; IO.println (Json.mkObj [("lookup",report)]).compress
      | .error e => IO.println (Json.mkObj [("lookup",Json.mkObj [("family",toJson family),("key",toJson (hex key)),("ABORTED",toJson e)])]).compress
  return 0
