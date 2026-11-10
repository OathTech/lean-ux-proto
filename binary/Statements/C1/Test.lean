import StatementC1Vacuity
import C1Interfaces

/-! Executable rendering of the C1 statement, revision 3. Not a proof
and not part of the package build: run with `Statements/C1/run-tests.sh`.

It executes the saved s5 instructions of the six functions with the
package's interpreter loop (`runUntil`, unchanged) and nothing else of the
runner: entry memory, the allocator and free, and every check are this
file's. Each call is judged in three steps, reported separately:

- PREMISE: the statement's own executable premises (`emptyTable`,
  `insertReady`, `lookupReady`) and, on every service transition, every
  clause of `AllocatorContract` against a concrete model of `Idle` held in
  arena memory. A run whose premises fail is no evidence either way.
- MIRROR: the mirror's own run; a refusal makes the clause silent.
- CONCLUSION: the machine-level conclusion of `InsertStep` / `LookupStep`
  (`Returned`, `eax`, the sequence word, `rax`, the write frame).

The search (`configs`) varies the layout, the entry state and the service
over families that meet the premises and looks for a broken conclusion.
`counterexampleH1` is a service that meets every clause of the revision 1
contract and breaks the conclusion; the revised contract refuses it.

Revision 3 adds: the separation of `ServiceReady` at every service entry and
the bound on the returned object (in `contractStep`); a service with a state
word in the arena judged at a plain and at an aliased entry state by
revisions 2 and 3 (`stateWordProbes`); the caller's reference moved between
peers during the scenario, and count changes the closed world does not
admit (`referenceStep`, `referenceProbes`); and `ServiceActive` evaluated on
the test service. -/
namespace Binary.Statements.C1.Test
open Lean Leanux Leanux.WG Binary Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-! ## Configurations -/

structure Config where
  name : String
  table : Nat := 0x100000
  peerBase : Nat := 0x600000
  arena : Nat := 0xa00000
  arenaSize : Nat := 0x100000
  spacing : Nat := 0x1000        -- distance between objects handed out
  stack : Nat := 0x400800
  keyAt : Nat := 0xb00000
  mode : Nat := 2                -- KCOV mode of the task: 0 off, 2 PC, 3 comparisons
  capacity : Nat := 0x400        -- coverage words
  fill : Nat := 0                -- coverage count word at the start
  preempt : Nat := 512
  seq : Nat := 0
  nextNode : Nat := 0
  refcount : Nat := 1
  rdxHigh : Nat := 0             -- garbage above the 8-bit prefix length
  direction : Bool := false      -- the direction flag at entry
  depth : Nat := 64              -- the allocator's stack scratch
  -- the service
  contractV1 : Bool := false     -- judge the service by the revision 1 contract
  contractV2 : Bool := false     -- judge it by the revision 2 contract (no separation, no bound on the object)
  clobberLive : Bool := false    -- clear the peer word of the oldest node handed out
  usesStack : Bool := true
  writesRecord : Bool := true
  scribble : Bool := true        -- garbage into free arena, the released object, caller-saved registers

def cacheValue : Nat := 0xc00000
def taskAddr : Nat := 0x800000
def coverageArea : Nat := 0x900000

def Config.layout (cfg : Config) : Layout :=
  ⟨cfg.table,(List.range 2).map (fun id => (id,cfg.peerBase+id*0x1000)),[(cfg.arena,cfg.arenaSize)],cacheValue⟩
def Config.allocator (cfg : Config) : Allocator := ⟨fun _ _ _ => True,cfg.depth⟩

/-! ## The allocator model: its state and its answers live in arena memory

`+0` bump pointer, `+8` free-list head, `+16` index of the next answer,
`+24` number of answers, `+32+2i` (site, outcome) of answer `i`. Released
objects are chained through their first word. -/

def metaSize : Nat := 0x1000
def word (m : DataMem) (a : Nat) : Except String Nat := readNat ⟨{dmem := m},0⟩ a 8

def freeList (m : DataMem) (head : Nat) : Nat → Except String (List Nat)
  | 0 => throw "idle.free-list-too-long"
  | fuel+1 => if head == 0 then pure [] else do
      return head :: (← freeList m (← word m head) fuel)

/-- The model of `Idle m live stream`. It reads only the allocator's block
and the released objects. -/
def idle (cfg : Config) (m : DataMem) (live : List Nat) (stream : List HiddenRecord) : Except String Unit := do
  let base := cfg.arena
  let bump ← word m base
  let free ← freeList m (← word m (base+8)) 64
  let index ← word m (base+16)
  let count ← word m (base+24)
  let mut answers := []
  for i in [index:count] do
    answers := answers ++ [(← readNat ⟨{dmem := m},0⟩ (base+32+2*i) 1,← readNat ⟨{dmem := m},0⟩ (base+33+2*i) 1)]
  require (answers == stream.map fun r => (r.site,(r.bytes.headD 2).toNat)) "idle.answers"
  require (base+metaSize ≤ bump && bump ≤ cfg.arena+cfg.arenaSize) "idle.bump"
  let objects := live ++ free
  require (objects.all fun o => base+metaSize ≤ o && o+nodeSize ≤ bump && o % 8 == 0) "idle.objects"
  require (objects.zipIdx.all fun (o,i) => (objects.drop (i+1)).all fun p => disjointRanges o nodeSize p nodeSize) "idle.overlap"

def inside (a n : Nat) (spans : List Pair.Span) : Bool := spans.any fun (b,k) => b ≤ a && a+n ≤ b+k

def returned (s t : MachineState) (ra : Nat) : Bool :=
  t.pc.toBitVec.toNat == ra && t.data.regs.rsp == s.data.regs.rsp+8 &&
  [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15].all fun reg => t.data.regs.get64 reg == s.data.regs.get64 reg

/-- The service the tests supply at `allocEntry` and `freeEntry`. Unlike the
runner's, it fails on an unmapped stack, uses its scratch, appends a word to
the coverage buffer when the buffer is in use, keeps its state in the arena,
reuses released objects and returns garbage in caller-saved registers.
Returns the new state, the objects handed out and every store it made. -/
def service (cfg : Config) (c : CommonBitsCoverage.Context) (s : MachineState) (live : List Nat) :
    Except String (MachineState × List Nat × List Pair.Span) := do
  let rsp := s.data.regs.rsp.toNat
  let ra ← readNat s rsp 8
  let base := cfg.arena
  let mut m := s.data.dmem
  let mut log : List Pair.Span := []
  if cfg.usesStack && cfg.depth > 0 then
    unless (List.range cfg.depth).all fun i => (m.get? (.ofNat 64 (rsp-1-i))).isSome do
      throw "service: store to unmapped stack"
    m := m.storeBytes (.ofNat 64 (rsp-cfg.depth)) (List.replicate cfg.depth 0xa5)
    log := (rsp-cfg.depth,cfg.depth) :: log
  if cfg.writesRecord && decide c.Needed then
    let area := c.coverage.area.toNat
    let count ← word m area
    if count+1 < c.coverage.capacity.toNat then
      m := put (put m (area+8*(count+1)) 8 0x1eaf) area 8 (count+1)
      log := (area+8*(count+1),8) :: (area,8) :: log
  let mut live := live
  let mut answer := 0xdead0000
  if s.pc == allocEntry then
    let index ← word m (base+16)
    let outcome ← readNat ⟨{dmem := m},0⟩ (base+33+2*index) 1
    m := put m (base+16) 8 (index+1)
    log := (base+16,8) :: log
    if outcome == 1 then
      let head ← word m (base+8)
      let mut a := head
      if head != 0 then
        m := put m (base+8) 8 (← word m head)
        log := (base+8,8) :: log
      else
        a ← word m base
        m := put m base 8 (a+cfg.spacing)
        log := (base,8) :: log
      m := m.storeBytes (.ofNat 64 a) (List.replicate nodeSize 0)
      log := (a,nodeSize) :: log
      if cfg.scribble && cfg.spacing ≥ nodeSize+8 then
        m := put m (a+nodeSize) 8 0x5c5c5c5c5c5c5c5c
        log := (a+nodeSize,8) :: log
      if cfg.clobberLive then
        if let some old := live.head? then
          m := put m old 8 0
          log := (old,8) :: log
      live := live ++ [a]
      answer := a
    else answer := 0
  else
    let a := s.data.regs.rsi.toNat
    if cfg.scribble then
      m := m.storeBytes (.ofNat 64 a) (List.replicate nodeSize 0x6b)
      log := (a,nodeSize) :: log
    m := put (put m a 8 (← word m (base+8))) (base+8) 8 a
    log := (a,8) :: (base+8,8) :: log
    live := live.erase a
  let junk : UInt64 := 0xbad0bad0bad0bad0
  let regs := {s.data.regs with rax := .ofNat answer,rsp := s.data.regs.rsp+8}
  let regs := if cfg.scribble then {regs with
    rcx := junk,rdx := junk,rsi := junk,rdi := junk,r8 := junk,r9 := junk,r10 := junk,r11 := junk} else regs
  return (⟨{s.data with dmem := m,regs},.ofNat ra⟩,live,log)

/-- One service transition judged against `AllocatorContract`: the clause's
premises, the service, then every conjunct of the clause's conclusion.
`contractV1` judges it by the revision 1 clauses (live objects in the write
set, no readiness), `contractV2` by revision 2's (readiness without the
separation, no bound on the object). Throws `PREMISE: …` when the service is not one the
statement speaks about. -/
def contractStep (cfg : Config) (L : Layout) (s : MachineState) (live : List Nat)
    (stream : List HiddenRecord) : Except String (MachineState × List Nat × List HiddenRecord × List Pair.Span) := do
  let premise (ok : Bool) (what : String) : Except String Unit :=
    if ok then pure () else throw s!"PREMISE: contract.{what}"
  let rsp := s.data.regs.rsp.toNat
  let c ← Common.readContext s.data.dmem
  let ra ← readNat s rsp 8
  let isAlloc := s.pc == allocEntry
  -- the clause's hypotheses
  premise (isAlloc || s.pc == freeEntry) "entry"
  premise (rsp % 8 == 0) "entry-frame"
  premise (Trie.coverageCheck c s.data.dmem) "coverage-at-entry"
  unless cfg.contractV1 do
    premise (if c.Needed then 0 < c.coverage.capacity.toNat else true) "ready.capacity"
    premise (s.data.system.bits[10] == false) "ready.direction-flag"
    premise ((List.range cfg.depth).all fun i => (s.data.dmem.get? (.ofNat 64 (rsp-cfg.depth+i))).isSome) "ready.stack-mapped"
  unless cfg.contractV1 || cfg.contractV2 do
    -- `ServiceReady.separated` (revision 3), on the spans that cover its byte sets
    let stack := [(rsp-cfg.depth,cfg.depth+8)]
    premise (spansApart stack L.arena) "ready.separated.stack-arena"
    premise (spansApart stack (Trie.readSpans c)) "ready.separated.stack-coverage"
    premise (spansApart (Trie.readSpans c) L.arena) "ready.separated.coverage-arena"
    premise (spansApart (Trie.writeSpans c) (Trie.metadataSpans c ++ [(preemptCountAddress.toNat,4)])) "ready.separated.buffer-metadata"
  premise (s.data.regs.rdi.toNat == L.cache) "cache"
  (idle cfg s.data.dmem live stream).mapError (s!"PREMISE: contract.{·}")
  if isAlloc then
    premise (s.data.regs.get (.low .rsi .W32) == 0xdc0#32) "flags"
    let record :: _ := stream | throw "PREMISE: contract.no-pending-record"
    premise (allocSites.contains (ra,record.site)) "alloc-site"
  else
    premise (ra == freeSite && live.contains s.data.regs.rsi.toNat) "free-arguments"
  -- the service; a failure here is a service that does not return
  let (t,live',log) ← (service cfg c s live).mapError (s!"PREMISE: contract.returns: {·}")
  -- the clause's conclusion
  premise (returned s t ra) "returned"
  let kept := if cfg.contractV1 then [] else if isAlloc then live else live.erase s.data.regs.rsi.toNat
  for (a,n) in log do
    let scratch := inside a n [(rsp-cfg.depth,cfg.depth)]
    let buffer := inside a n (Trie.writeSpans c)
    let arena := inside a n L.arena && kept.all fun object => disjointRanges a n object nodeSize
    premise (scratch || buffer || arena) s!"writes: {a}+{n} is outside the service's write set"
  premise (Trie.coverageCheck c t.data.dmem) "coverage-after"
  let rest := if isAlloc then stream.drop 1 else stream
  if isAlloc then
    let a := t.data.regs.rax.toNat
    match (stream.head?.bind (·.bytes.head?)) with
    | some 0 => premise (a == 0 && live' == live) "alloc-null"
    | some 1 => premise (a != 0 && a % 8 == 0 && (cfg.contractV1 || cfg.contractV2 || a + nodeSize < 2^64) &&
        inside a nodeSize L.arena &&
        live.all (fun other => disjointRanges a nodeSize other nodeSize) &&
        (← readNat t a nodeSize) == 0 && live' == live ++ [a]) "alloc-object"
    | _ => pure ()
  else premise (live' == live.erase s.data.regs.rsi.toNat) "free-result"
  (idle cfg t.data.dmem live' rest).mapError (s!"PREMISE: contract.after.{·}")
  return (t,live',rest,log)

/-! ## Building a physically empty table -/

def outcomeRecord (site : Nat) (ok : Bool) : HiddenRecord := ⟨70+site,(if ok then 1 else 0)::List.replicate 39 0⟩

def emptyWorld (cfg : Config) (stream : List HiddenRecord) : World :=
  let peers := (List.range 2).foldl (fun peers id => peers.insert id {
    remoteStatic := List.replicate 32 0,presharedKey := List.replicate 32 0,
    precomputedStaticStatic := List.replicate 32 0,internalId := id,refcount := cfg.refcount})
    ({} : Std.TreeMap PeerId Peer)
  let dev : Device := {
    ifindex := 1,ifname := "wg0",peers,nextNode := cfg.nextNode,
    peerAllowedips := {seq := .ofNat cfg.seq}}
  let ambient : Ambient := {
    env := Runner.harnessEnv,timing := Env.timing,hidden := some stream,
    allocArmed := ["allocNode190","allocNode205","allocNode234"]}
  {ambient,tasks := Runner.initialTasks 1024 false false false,fs := {},wg := {dev := some dev}}

def emptyMemory (cfg : Config) (stream : List HiddenRecord) : DataMem := Id.run do
  let L := cfg.layout
  let mut m : DataMem := (List.replicate 0x1000 (0 : UInt8)).At (.ofNat 64 (cfg.stack-0x800))
  m := put m preemptCountAddress.toNat 4 cfg.preempt
  m := put m currentTaskAddress.toNat 8 taskAddr
  m := put m softirqPendingAddress.toNat 2 0
  m := put m (taskAddr+0x6e0) 4 cfg.mode
  m := put m (taskAddr+0x6e4) 4 cfg.capacity
  m := put m (taskAddr+0x6e8) 8 coverageArea
  m := put m (taskAddr+0x704) 4 0
  m := m.storeBytes (.ofNat 64 coverageArea) (List.replicate (8*cfg.capacity) 0)
  if cfg.capacity > 0 then m := put m coverageArea 8 cfg.fill
  m := m.storeBytes (.ofNat 64 L.table) (List.replicate AllowedipsMutationLayout.tableSize 0)
  m := put m (L.table+AllowedipsMutationLayout.seq) 8 cfg.seq
  for (_,a) in L.peers do
    m := m.storeBytes (.ofNat 64 a) (List.replicate Layouts.peerSize 0)
    m := put m (a+Root.nodeOffsets.peerRefcount) 4 cfg.refcount
    let head := a+AllowedipsMutationLayout.allowedips_list
    m := put (put m head 8 head) (head+8) 8 head
  m := put m cacheWord 8 cacheValue
  m := m.storeBytes (.ofNat 64 cfg.arena) (List.replicate metaSize 0)
  m := put m cfg.arena 8 (cfg.arena+metaSize)
  m := put m (cfg.arena+24) 8 stream.length
  for (r,i) in stream.zipIdx do
    m := put (put m (cfg.arena+32+2*i) 1 r.site) (cfg.arena+33+2*i) 1 (r.bytes.headD 2).toNat
  return m

/-! ## One call of the machine -/

structure Thread where
  memory : DataMem
  world : World
  live : List Nat
  names : Allowedips.Names
  deepest : Nat := 0

def storeKey (m : DataMem) (at' width key : Nat) : DataMem :=
  m.storeBytes (.ofNat 64 at') ((List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256))

def system (cfg : Config) : SystemFlags := {bits := if cfg.direction then 1 <<< 10 else 0}

/-- The proof plan's machine cut (`C1Interfaces.NodeCut`, `Exits`), its
decidable part, on the states one insertion visits: the common exit
`add+0x549` is reached once, in flight, with the answer in `ebx`; for the
cases that keep going below the first allocation on a nonempty trie, the
landed `NodeInit.boundary` holds at `add+0x156` against the mirror's device
with the sequence incremented, the new object is in the arena, `rbx` is the
placed node, and the common exit has the cut's stack pointer and the cut's
bytes from `rsp+48` up to and including the wrapper's return word. -/
def cutCheck (L : Layout) (names : Allowedips.Names) (w : World) (s : MachineState)
    (history : Array MachineState) (case : Proof.Case) (family key cidr pid : Nat) (answer : Int) :
    Except String Unit := do
  let add := AllowedipsMutationImage.Add.entry
  let top := s.data.regs.rsp.toNat
  let exits := history.filter (·.pc == add + 0x549)
  let some x := exits[0]? | throw "no state at the common exit"
  require (exits.size == 1) "the common exit is reached more than once"
  require (x.data.regs.get (.low .rbx .W32) == BitVec.ofInt 32 answer) "ebx at the common exit is not the answer"
  require (x.data.regs.rsp.toNat ≤ top && top ≤ x.data.regs.rsp.toNat + insertWindow) "InFlight at the common exit"
  let cuts := history.filter (·.pc == add + 0x156)
  if case == .child || case == .cover || case == .split || case == .splitNoMem then
    let some e := cuts[0]? | throw "no state at add+0x156"
    require (cuts.size == 1) "add+0x156 is reached more than once"
    let some d := w.wg.dev | throw "no device"
    let base ← (NodeInit.boundary names Root.nodeOffsets (Proof.bumped w d) e key cidr pid).mapError
      (s!"NodeInit.boundary: {·}")
    require (L.arena.any fun span => span.1 ≤ base && base+nodeSize ≤ span.1+span.2) "the new object is not in the arena"
    let (placed,_) := Proof.walkOf w d family key cidr
    let address ← Trie.address names.trie.nodes placed
    require (address == e.data.regs.rbx.toNat) "rbx at the cut is not the placed node"
    require (e.data.regs.rsp.toNat ≤ top && top ≤ e.data.regs.rsp.toNat + insertWindow) "InFlight at the cut"
    require (e.data.system.bits[10] == false) "direction flag at the cut"
    require (x.data.regs.rsp == e.data.regs.rsp) "the stack pointer at the common exit is not the cut's"
    let low := e.data.regs.rsp.toNat + 48
    require (x.data.dmem.loadBytes (.ofNat 64 low) (top+8-low) == e.data.dmem.loadBytes (.ofNat 64 low) (top+8-low))
      "a word between the cut's rsp+48 and the wrapper's return word changed before the common exit"
  else require cuts.isEmpty s!"add+0x156 is reached in case {repr case}"

def insertCall (cfg : Config) (input : Input) (seed : UInt64) (th : Thread)
    (family key cidr pid : Nat) (related : Bool) : Except String (Thread × Int) := do
  let L := cfg.layout
  let A := cfg.allocator
  let width := if family == 4 then 32 else 128
  let peer ← Trie.address L.peers (some pid)
  let memory := storeKey (put th.memory cfg.stack 8 stopAddr) cfg.keyAt width key
  let initial : MachineState := ⟨{dmem := memory,system := system cfg,regs := {
    rdi := .ofNat L.table,rsi := .ofNat cfg.keyAt,rdx := .ofNat (cfg.rdxHigh*256+cidr),
    rcx := .ofNat peer,r8 := 0x7777,rsp := .ofNat cfg.stack,
    rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},
    .ofNat (if family == 4 then input.insert4 else input.insert6)⟩
  let c ← Common.readContext initial.data.dmem
  (insertReady L A c initial family key cidr pid (.ofNat stopAddr)).mapError (s!"PREMISE: {·}")
  let some stream := th.world.ambient.hidden | throw "PREMISE: no pending records"
  let (answer,w') ← ((liftWG (WG.insert family key cidr pid)).run th.world).mapError (s!"MIRROR: {Stop.message ·}")
  -- the proof plan's derived facts about the mirror's walk (C1Invariant), before the call
  if related then (Proof.walkCheck th.world family key cidr).mapError (s!"INVARIANT: {·}")
  -- the mirror's run is the proof plan's pure step (C1Step), up to `Allowedips.target`
  let case ← (Proof.stepCheck th.world family key cidr pid answer w').mapError (s!"INVARIANT: {·}")
  -- the machine
  let mut r : Run := {state := initial}
  let mut live := th.live
  let mut names := th.names
  let mut pending := stream
  let mut log : List Pair.Span := []
  for _ in [:4] do
    r ← (runUntil input.lookup.instructions input.lookup.labels input.lookup.hooks input.lookup.preempt
      r.state seed true input.lookup.budget cfg.preempt #[input.alloc,input.free] (some r) stopAddr
      (some #[(AllowedipsMutationImage.Add.entry+0x156).toBitVec.toNat,
        (AllowedipsMutationImage.Add.entry+0x549).toBitVec.toNat])).mapError
      (s!"CONCLUSION: the machine does not return: {·}")
    if r.state.pc.toBitVec.toNat == stopAddr then break
    let entry := r.state
    let (t,live',rest,stores) ← contractStep cfg L entry live pending
    if entry.pc == allocEntry then
      if t.data.regs.rax.toNat != 0 then names := names.allocated t.data.regs.rax.toNat
    else names := {names with trie := {names.trie with
      nodes := names.trie.nodes.filter (·.2 != entry.data.regs.rsi.toNat)}}
    -- a service returns to add+0x156: that state is the proof plan's cut
    r := {r with state := t,history := if t.pc == AllowedipsMutationImage.Add.entry+0x156 then r.history.push t else r.history}
    live := live'; pending := rest; log := log ++ stores
  let t := r.state
  let conclusion (ok : Bool) (what : String) : Except String Unit :=
    if ok then pure () else throw s!"CONCLUSION: {what}"
  conclusion (t.pc.toBitVec.toNat == stopAddr) "the machine does not return (service budget)"
  conclusion (returned initial t stopAddr) "Returned"
  conclusion (t.data.regs.get (.low .rax .W32) == BitVec.ofInt 32 answer)
    s!"eax {t.data.regs.get (.low .rax .W32)} is not the mirror's {answer}"
  let seq := L.table+AllowedipsMutationLayout.seq
  conclusion ((← readNat t seq 8) == ((← readNat initial seq 8)+1) % 2^64) "SeqAdvanced"
  let window := insertWindow+A.depth
  let frame := [(cfg.stack-window,window)] ++ Trie.writeSpans c ++ L.heap
  for (a,n) in r.writes.toList ++ log do
    conclusion (inside a n frame) s!"a write at {a}+{n} is outside InsertWrites"
  require (w'.ambient.hidden == some pending) "MODEL: the mirror and the allocator model disagree on the pending records"
  if related then
    (assertAt names Root.nodeOffsets t.data.dmem w').mapError (s!"RELATED: {·}")
    require (names.trie.nodes.map (·.2) == live) "RELATED: names and handed-out objects differ"
    -- the proof plan's invariant (C1Invariant.Inv, its decidable part) and the ordering facts
    (Proof.invCheck L names w' t.data.dmem).mapError (s!"INVARIANT: {·}")
    (cutCheck L th.names th.world initial r.history case family key cidr pid answer).mapError (s!"CUT: {·}")
  let deepest := r.writes.foldl (fun low (a,_) => if cfg.stack-4096 ≤ a && a < cfg.stack then min low a else low) cfg.stack
  return ({memory := t.data.dmem,world := w',live,names,deepest := max th.deepest (cfg.stack-deepest)},answer)

def lookupCall (cfg : Config) (input : Input) (seed : UInt64) (th : Thread)
    (family key : Nat) : Except String (Thread × Nat) := do
  let L := cfg.layout
  let some d := th.world.wg.dev | throw "PREMISE: no device"
  let width := if family == 4 then 32 else 128
  let slot := L.table+(if family == 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6)
  let memory := storeKey (put th.memory cfg.stack 8 stopAddr) cfg.keyAt width key
  let regs : Reg64s := {
    rdi := .ofNat (← word memory slot),rsi := .ofNat width,rdx := .ofNat cfg.keyAt,rsp := .ofNat cfg.stack,
    rbx := 0x11,rbp := 0x22,r12 := 0x33,r13 := 0x44,r14 := 0x55,r15 := 0x66}
  let initial : MachineState := ⟨{regs,dmem := memory,system := system cfg},.ofNat input.lookup.entry⟩
  let c ← Common.readContext initial.data.dmem
  (lookupReady L c initial family key (.ofNat stopAddr)).mapError (s!"PREMISE: {·}")
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let (answer,w') ← ((Source.lookup root width key).run th.world).mapError (s!"MIRROR: {Stop.message ·}")
  let pointer ← Trie.address L.peers answer
  let r ← (runUntil input.lookup.instructions input.lookup.labels input.lookup.hooks input.lookup.preempt
    initial seed true input.lookup.budget cfg.preempt #[] none stopAddr (some #[])).mapError
    (s!"CONCLUSION: the machine does not return: {·}")
  let t := r.state
  unless returned initial t stopAddr do throw "CONCLUSION: Returned (lookup)"
  unless t.data.regs.rax.toNat == pointer do
    throw s!"CONCLUSION: lookup returns {t.data.regs.rax.toNat}, the mirror's peer is at {pointer}"
  let frame := [(cfg.stack-lookupWindow,lookupWindow)] ++ Trie.callBuffers c ++
    [(preemptCountAddress.toNat,4)] ++ L.heap
  for (a,n) in r.writes do
    unless inside a n frame do throw s!"CONCLUSION: a write at {a}+{n} is outside LookupWrites"
  return ({th with memory := t.data.dmem,world := w'},pointer)

/-! ## The caller's reference on a peer (revision 3: `Referenced`) -/

/-- `CountMoved`, executably: both counts readable with the stated values and
every other heap byte the same. -/
def countMoved (L : Layout) (pid before after : Nat) (m m' : DataMem) : Except String Unit := do
  let peer ← Trie.address L.peers (some pid)
  let word := peer+Root.nodeOffsets.peerRefcount
  require ((← readNat ⟨{dmem := m},0⟩ word 4) == before) s!"count-before: not {before}"
  require ((← readNat ⟨{dmem := m'},0⟩ word 4) == after) s!"count-after: not {after}"
  for (a,n) in L.heap do
    for i in [:n] do
      unless word ≤ a+i && a+i < word+4 do
        unless m.get? (.ofNat 64 (a+i)) == m'.get? (.ofNat 64 (a+i)) do
          throw s!"heap: byte {a+i} differs"

/-- One step of `Referenced`, judged like a call. PREMISE: a drop starts
above one; the count word moves by one and no other heap byte changes
(`after` is the memory offered, by default the count word rewritten);
MIRROR: the mirror's `peerGet` / `peerPut` on that peer; CONCLUSION: the
invariant's decidable part (`Proof.relatedCheck`) for the mirror's world
after the step and the memory after it. -/
def referenceStep (cfg : Config) (th : Thread) (pid : Nat) (drop : Bool)
    (after : Option DataMem := none) (mirror : Bool := true) : Except String Thread := do
  let L := cfg.layout
  let peer ← (Trie.address L.peers (some pid)).mapError (s!"PREMISE: referenced.peer: {·}")
  let word := peer+Root.nodeOffsets.peerRefcount
  let count ← readNat ⟨{dmem := th.memory},0⟩ word 4
  if drop && !(1 < count) then throw "PREMISE: referenced.last-reference"
  let next := if drop then count-1 else count+1
  let memory := after.getD (put th.memory word 4 next)
  let world ← if mirror then
      ((liftWG (if drop then WG.peerPut (some pid) else WG.peerGet pid)).run th.world).map (·.2)
        |>.mapError (s!"MIRROR: {Stop.message ·}")
    else pure th.world
  unless mirror do throw "PREMISE: referenced.unpaired: no mirror step"
  (countMoved L pid count next th.memory memory).mapError (s!"PREMISE: referenced.{·}")
  (Proof.relatedCheck L th.names world memory).mapError (s!"CONCLUSION: Referenced: {·}")
  return {th with memory,world}

/-! ## The scenario -/

def scenario (family : Nat) : List (String × Nat × Nat × Nat × List HiddenRecord) :=
  let width := if family == 4 then 32 else 128
  let key (value : Nat) := value*2^(width-32)
  let yes := fun site => outcomeRecord site true
  let no := fun site => outcomeRecord site false
  [("invalid-prefix",0,width+1,0,[]),
   ("empty-allocation-failure",key 0x0a000000,24,0,[no 7]),
   ("empty-root",key 0x0a000000,24,0,[yes 7]),
   ("exact-reassignment",key 0x0a000055,24,1,[]),
   ("exact-same-peer-single",key 0x0a000055,24,1,[]),
   ("first-child",key 0x0a000001,32,0,[yes 8]),
   ("other-child",key 0x0a000081,32,1,[yes 8]),
   ("exact-same-peer-move-tail",key 0x0a000055,24,1,[]),
   ("covering-root",key 0x0a000000,16,0,[yes 8]),
   ("intermediate-root",key 0x0b000001,32,1,[yes 8,yes 9]),
   ("rollback",key 0x0c000001,32,0,[yes 8,no 9]),
   ("newnode-allocation-failure",key 0x0d000001,32,0,[no 8]),
   ("intermediate-becomes-peer",key 0x0a000000,7,0,[]),
   ("intermediate-child-and-reuse",key 0x0a000040,32,0,[yes 8,yes 9]),
   ("covering-below-parent",key 0x0a000080,25,1,[yes 8]),
   ("child-below-covering",key 0x0a0000c0,27,0,[yes 8]),
   ("default-route",0,0,1,[yes 8]),
   ("host-bits-set",key 0x0affffff,9,0,[yes 8,yes 9])]

structure Outcome where
  insertions : Nat := 0
  lookups : Nat := 0
  deepest : Nat := 0
  decisions : List String := []
  moves : Nat := 0

/-- From a physically empty table: every insertion of the scenario in turn,
the mirror world and its pending records threaded from call to call as the
statement threads them, and after each insertion lookups of that address
and of up to four addresses inserted earlier. `families` interleaves when it holds both. -/
def runConfig (cfg : Config) (input : Input) (seed : UInt64) (families : List Nat)
    (related : Bool := true) (moves : Bool := false) : Except String Outcome := do
  let calls := (scenario 4).zip (scenario 6) |>.flatMap fun (a,b) =>
    (if families.contains 4 then [(4,a)] else []) ++ (if families.contains 6 then [(6,b)] else [])
  let stream := calls.flatMap fun (_,_,_,_,_,records) => records
  let w := emptyWorld cfg stream
  let m := emptyMemory cfg stream
  let L := cfg.layout
  let some d := w.wg.dev | throw "PREMISE: no device"
  (emptyTable L m d).mapError (s!"PREMISE: {·}")
  require (armed w && stream.all fun r => (allocSites.map (·.2)).contains r.site) "PREMISE: Initial"
  (idle cfg m [] stream).mapError (s!"PREMISE: {·}")
  let mut th : Thread := {memory := m,world := w,live := [],names := ⟨L.table,⟨[],L.peers⟩,cfg.nextNode⟩}
  let mut out : Outcome := {}
  let mut seen : List (Nat × Nat) := []
  let mut holder : Option Nat := none
  for (family,label,address,cidr,pid,_) in calls do
    -- as `set_peer` does over existing peers: the caller's reference follows the peer being configured
    if moves && holder != some pid then
      let mut next := th
      let mut done := 0
      let mut silent := false
      for (peer,drop) in (holder.map (·,true)).toList ++ [(pid,false)] do
        unless silent do
          match referenceStep cfg next peer drop with
          | .ok after => next := after; done := done+1
          | .error e => if e.startsWith "MIRROR" then silent := true else throw s!"{e} [reference move before {label}/v{family}]"
      unless silent do
        th := next; holder := some pid; out := {out with moves := out.moves+done}
    let before := th.world.steps.size
    let (after,_) ← (insertCall cfg input seed th family address cidr pid related).mapError
      (fun e => s!"{e} [{label}/v{family}]")
    out := {out with insertions := out.insertions+1,decisions := out.decisions ++
      ((after.world.steps.toList.drop before).filterMap fun step =>
        let name := toString (repr step.decision)
        if name.startsWith "Leanux.Decision.add" then some s!"{name.drop 19}={step.outcome}" else none)}
    th := after
    seen := (seen.filter (· != (family,address))) ++ [(family,address)]
    -- the address just inserted and the three inserted longest ago and most recently before it
    let probes := (seen.take 2 ++ (seen.drop 2).reverse.take 3).eraseDups
    for (f,k) in probes do
      match lookupCall cfg input seed th f k with
      | .ok (next,_) => th := next; out := {out with lookups := out.lookups+1}
      | .error e => if e.startsWith "MIRROR" then pure () else throw s!"{e} [lookup of {k}/v{f} after {label}/v{family}]"
  return {out with deepest := th.deepest}

/-! ## Revision 3's probes -/

/-- An entry state of the allocation service built by hand: the empty table's
memory, a return word for site 77 at `stack`, the cache and the flags. -/
def serviceEntry (cfg : Config) (records : List HiddenRecord) (stack : Nat) (memory : DataMem → DataMem := id) :
    MachineState :=
  ⟨{dmem := memory (put (emptyMemory cfg records) stack 8 0xffffffff813a0ff2),
    regs := {rdi := .ofNat cacheValue,rsi := 0xdc0,rsp := .ofNat stack}},allocEntry⟩

def changed (s t : MachineState) (spans : List Pair.Span) : Bool :=
  spans.any fun (a,n) => (List.range n).any fun i =>
    s.data.dmem.get? (.ofNat 64 (a+i)) != t.data.dmem.get? (.ofNat 64 (a+i))

/-- Change 4. The test service keeps an index of its next answer at
`arena+16` and advances it on every allocation: ordinary internal state.
(1) At a plain entry state it meets every clause of revisions 2 and 3.
(2) At the aliased state of the service package's finding (the current-task
word moved so that the task's mode field is the index word, the preemption
count cleared) revision 2 admits the state and the service then breaks
`c.At`: under revision 2 this service did not meet the contract.
Revision 3 refuses the aliased state (`ServiceReady.separated`).
(3) A state whose stack scratch lies in the arena is refused by revision 3.
Also `ServiceActive`'s two changed bytes, on the plain state. -/
def stateWordProbes : Except String (List String) := do
  let cfg : Config := {name := "state word"}
  let records := [outcomeRecord 7 true]
  let L := cfg.layout
  let index (s : MachineState) := readNat s (cfg.arena+16) 8
  let mut lines := []
  let plain := serviceEntry cfg records cfg.stack
  for (revision,v2) in [(2,true),(3,false)] do
    match contractStep {cfg with contractV2 := v2} L plain [] records with
    | .ok (t,_,_,_) =>
      require ((← index plain) == 0 && (← index t) == 1) "state word: the index did not advance"
      lines := lines ++ [s!"state word, revision {revision} contract, plain entry state: every clause met; the index at arena+16 went 0 -> 1"]
      if revision == 3 then
        let c ← Common.readContext plain.data.dmem
        let rsp := plain.data.regs.rsp.toNat
        require (decide c.Needed && 0 < cfg.depth && changed plain t [(rsp-cfg.depth,cfg.depth)] &&
          changed plain t (Trie.writeSpans c)) "ServiceActive: the test service did not change a scratch byte and a buffer byte"
        lines := lines ++ ["witness: ServiceActive holds of the test service at that state (buffer in use, a scratch byte and a buffer byte changed, returned)"]
    | .error e => throw s!"state word: revision {revision}, plain state: {e}"
  let quiet : Config := {cfg with usesStack := false,writesRecord := false}
  match contractStep quiet L plain [] records with
  | .ok (t,_,_,_) =>
    let c ← Common.readContext plain.data.dmem
    require (!changed plain t [(cfg.stack-cfg.depth,cfg.depth)] && !changed plain t (Trie.writeSpans c))
      "ServiceActive: the quiet service changed a scratch or buffer byte"
    lines := lines ++ ["witness: ServiceActive fails of the quiet service (no scratch byte, no buffer byte changed)"]
  | .error e => throw s!"state word: the quiet service: {e}"
  let aliased := serviceEntry cfg records cfg.stack fun m =>
    put (put m currentTaskAddress.toNat 8 (cfg.arena+16-0x6e0)) preemptCountAddress.toNat 4 0
  for (revision,v2,expected) in [(2,true,"PREMISE: contract.coverage-after"),(3,false,"PREMISE: contract.ready.separated.coverage-arena")] do
    match contractStep {cfg with contractV2 := v2} L aliased [] records with
    | .error e =>
      require (e.startsWith expected) s!"state word: revision {revision}, aliased state: {e}"
      lines := lines ++ [s!"state word, revision {revision} contract, aliased entry state: " ++
        (if v2 then s!"state admitted, the service does not conform: {e}" else s!"state refused: {e}")]
    | .ok _ => throw s!"state word: revision {revision}, aliased state: the clause holds"
  let inArena := serviceEntry cfg records (cfg.arena+0x800)
  match contractStep cfg L inArena [] records with
  | .error e =>
    require (e.startsWith "PREMISE: contract.ready.separated.stack-arena") s!"separation: stack in the arena: {e}"
    lines := lines ++ [s!"separation, revision 3 contract, stack scratch inside the arena: state refused: {e}"]
  | .ok _ => throw "separation: a stack inside the arena is admitted"
  return lines

/-- Change 2. From an empty table with two peers at count 2: steps the
closed world admits, and count changes it does not. -/
def referenceProbes : Except String (List String) := do
  let cfg : Config := {name := "references",refcount := 2,arenaSize := 0x1000+72*40}
  let stream := [outcomeRecord 7 true]
  let L := cfg.layout
  let names : Allowedips.Names := ⟨L.table,⟨[],L.peers⟩,cfg.nextNode⟩
  let th : Thread := {memory := emptyMemory cfg stream,world := emptyWorld cfg stream,live := [],names}
  (Proof.relatedCheck L th.names th.world th.memory).mapError (s!"references: the start: {·}")
  let word (pid : Nat) := cfg.peerBase+pid*0x1000+Root.nodeOffsets.peerRefcount
  let mut lines := []
  -- admitted: a reference moved from peer 0 to peer 1
  let moved ← referenceStep cfg (← referenceStep cfg th 0 true) 1 false
  require ((← readNat ⟨{dmem := moved.memory},0⟩ (word 0) 4) == 1 && (← readNat ⟨{dmem := moved.memory},0⟩ (word 1) 4) == 3)
    "references: the counts after the move"
  lines := lines ++ ["references: peerPut 0 (2 -> 1) then peerGet 1 (2 -> 3), each paired with its count word: accepted, the invariant's decidable part holds after each"]
  let refused (what : String) (expected : String) (result : Except String Thread) : Except String String :=
    match result with
    | .error e => if e.startsWith expected then pure s!"references, refused: {what}: {e}" else throw s!"references: {what}: {e}"
    | .ok _ => throw s!"references: {what}: accepted"
  let raised := put th.memory (word 0) 4 3
  lines := lines ++ [← refused "a count raised in memory with no mirror step" "PREMISE: referenced.unpaired"
    (referenceStep cfg th 0 false (mirror := false))]
  -- and the invariant's decidable part does not survive it, nor a mirror step without the memory change
  let (_,taken) ← ((liftWG (WG.peerGet 0)).run th.world).mapError Stop.message
  require (!(Proof.relatedCheck L th.names th.world raised).isOk && !(Proof.relatedCheck L th.names taken th.memory).isOk)
    "references: an unpaired change keeps the invariant's decidable part"
  lines := lines ++ ["references: the invariant's decidable part fails after a count change without the mirror step, and after the mirror step without the count change"]
  lines := lines ++ [← refused "a count raised by two with one peerGet" "PREMISE: referenced.count-after"
    (referenceStep cfg th 0 false (after := some (put th.memory (word 0) 4 4)))]
  lines := lines ++ [← refused "a paired peerGet with a root word changed as well" "PREMISE: referenced.heap"
    (referenceStep cfg th 0 false (after := some (put raised (cfg.table+AllowedipsMutationLayout.root4) 8 0xa01000)))]
  lines := lines ++ [← refused "a paired peerGet with an arena byte changed as well" "PREMISE: referenced.heap"
    (referenceStep cfg th 0 false (after := some (put raised (cfg.arena+16) 1 9)))]
  let last ← referenceStep cfg th 0 true
  lines := lines ++ [← refused "the last reference dropped (1 -> 0)" "PREMISE: referenced.last-reference"
    (referenceStep cfg last 0 true)]
  lines := lines ++ [← refused "a reference on a peer the layout does not name" "PREMISE: referenced.peer"
    (referenceStep cfg th 7 false)]
  return lines

/-! ## The search: families that meet the premises -/

def high : Config := {
  name := "kernel-range addresses for the table, peers, arena, stack and address bytes",
  table := 0xffff888004a01000,peerBase := 0xffff888005230000,arena := 0xffff888006400000,
  stack := 0xffffc90000147e00,keyAt := 0xffff888007001004}

def configs : List Config := [
  {name := "baseline: the fixture's addresses, PC coverage, a service that uses its stack and writes a record"},
  {name := "objects packed 72 bytes apart",spacing := 72},
  {name := "objects 80 bytes apart, the 8 bytes between them scribbled",spacing := 80},
  high,
  {high with name := "kernel-range addresses, objects packed",spacing := 72},
  {name := "comparison coverage (mode 3)",mode := 3},
  {name := "coverage off (mode 0)",mode := 0},
  {name := "coverage buffer full from the start",fill := 0x3ff},
  {name := "coverage buffer filling up during the run",fill := 0x3c0},
  {name := "coverage capacity of two words",capacity := 2},
  {name := "process context (preempt count 0)",preempt := 0},
  {name := "nested BH-disable (preempt count 1024)",preempt := 1024},
  {name := "sequence word about to wrap",seq := 2^64-1},
  {name := "garbage above the prefix-length byte",rdxHigh := 0xabcdef},
  {name := "address bytes directly above the return word",keyAt := 0x400808},
  {name := "address bytes directly below the stack window",keyAt := 0x400800-insertWindow-64-16},
  {name := "stack 8 mod 16",stack := 0x400808,keyAt := 0xb00000},
  {name := "table directly below the arena",table := 0xa00000-24},
  {name := "a small arena, objects packed",arenaSize := 0x1000+72*40,spacing := 72},
  {name := "large allocation counter and reference count in the mirror",nextNode := 1000,refcount := 0x7ffffff0},
  {name := "no stack scratch",depth := 0},
  {name := "a deep stack scratch",depth := 512},
  {name := "a quiet service (no stack use, no record, no scribbling)",usesStack := false,writesRecord := false,scribble := false}]

end Binary.Statements.C1.Test

open Lean Binary Binary.Pair Binary.Pair.Allowedips Binary.Statements.C1 Binary.Statements.C1.Test in
def main (args : List String) : IO UInt32 := do
  -- a second argument `probes` skips the search over the 23 families (section 1) and runs the rest
  let (path,searched) ← match args with
    | [path] => pure (path,configs)
    | [path,"probes"] => pure (path,[])
    | _ => IO.eprintln "usage: Test INPUT.json [probes] (binary/allowedips_mutation.py writes the input)"; return 1
  let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Input))
  unless input.alloc == allocEntry.toBitVec.toNat && input.free == freeEntry.toBitVec.toNat &&
      input.cacheWord == cacheWord && input.freeReturn == freeSite &&
      input.allocationReturns.toList.all (fun (a,site) => allocSites.contains (a,70+site)) &&
      input.allocationReturns.size == allocSites.length &&
      input.insert4 == Binary.AllowedipsMutationImage.Insert4.entry.toBitVec.toNat &&
      input.insert6 == Binary.AllowedipsMutationImage.Insert6.entry.toBitVec.toNat do
    IO.eprintln "FAIL: statement addresses differ from the ELF-derived input"; return 1
  IO.println "addresses: statement literals equal the ELF-derived input"
  let mut failed := false
  -- 1. the statement as written, over the search's configurations
  for cfg in searched do
    let runs := if cfg.name.startsWith "baseline" then [((0 : UInt64),[4]),(0,[6]),(0,[4,6]),(0xffffffffffffffff,[4,6])]
      else [((0 : UInt64),[4,6])]
    let mut insertions := 0
    let mut lookups := 0
    let mut deepest := 0
    let mut verdict := "holds"
    let mut decisions : List String := []
    for (seed,families) in runs do
      match runConfig cfg input seed families with
      | .ok out =>
        insertions := insertions+out.insertions; lookups := lookups+out.lookups
        deepest := max deepest out.deepest; decisions := (decisions ++ out.decisions).eraseDups
      | .error e =>
        verdict := e
        unless e.startsWith "PREMISE" do failed := true
        break
    IO.println s!"search: {cfg.name}: {verdict} ({insertions} insertions, {lookups} lookups, deepest stack write {deepest}, {decisions.length} distinct mirror decisions)"
    (← IO.getStdout).flush
  -- 2. premises that must refuse
  for cfg in [({name := "direction flag set at entry",direction := true} : Config),
      {name := "address bytes inside the stack window",keyAt := 0x400800-64},
      {name := "arena over the table",arena := 0x100000-0x1000},
      {name := "coverage capacity zero with the buffer in use",capacity := 0},
      {name := "stack too shallow for the allocator's scratch",depth := 4096}] do
    match runConfig cfg input 0 [4] with
    | .error e =>
      if e.startsWith "PREMISE" then IO.println s!"refused: {cfg.name}: {e}"
      else do failed := true; IO.println s!"FAIL: {cfg.name}: {e}"
    | .ok _ => do failed := true; IO.println s!"FAIL: {cfg.name}: accepted"
  -- 3. H1: a service meeting every clause of the revision 1 contract that clears an older node
  let evil : Config := {name := "H1",clobberLive := true}
  match runConfig {evil with contractV1 := true} input 0 [4] (related := false) with
  | .error e =>
    if e.startsWith "CONCLUSION" then IO.println s!"counterexample H1, revision 1 contract: every premise met, {e}"
    else do failed := true; IO.println s!"FAIL: H1 under the revision 1 contract: {e}"
  | .ok _ => do failed := true; IO.println "FAIL: H1 under the revision 1 contract: conclusion holds"
  match runConfig evil input 0 [4] (related := false) with
  | .error e =>
    if e.startsWith "PREMISE: contract.writes" then IO.println s!"counterexample H1, revision 3 contract (the clause is revision 2's): excluded, {e}"
    else do failed := true; IO.println s!"FAIL: H1 under the revision 3 contract: {e}"
  | .ok _ => do failed := true; IO.println "FAIL: H1 under the revision 3 contract: accepted"
  -- 4. H2: a state meeting every hypothesis of the revision 1 `alloc` clause, with nothing
  -- mapped below the return word; a service that uses its stack cannot return from it
  let lone := 0x700000
  let records := [outcomeRecord 7 true]
  let probe : Config := {name := "H2"}
  let entry : MachineState := ⟨{
    dmem := put (emptyMemory probe records) lone 8 0xffffffff813a0ff2,
    regs := {rdi := .ofNat cacheValue,rsi := 0xdc0,rsp := .ofNat lone}},allocEntry⟩
  for v1 in [true,false] do
    match contractStep {probe with contractV1 := v1} probe.layout entry [] records with
    | .error e =>
      if (v1 && e.startsWith "PREMISE: contract.returns") || (!v1 && e.startsWith "PREMISE: contract.ready.stack-mapped") then
        IO.println s!"probe H2, revision {if v1 then 1 else 3} contract (the premise is revision 2's): {e}"
      else do failed := true; IO.println s!"FAIL: H2 probe: {e}"
    | .ok _ => do failed := true; IO.println "FAIL: H2 probe: the service returned"
  -- 5. the frame law on the model, and its teeth
  let cfg : Config := {name := "frame"}
  let stream := [outcomeRecord 7 true]
  let m := emptyMemory cfg stream
  let outside := put m (cfg.table+16) 8 99
  let inMeta := put m (cfg.arena+16) 8 1
  unless (idle cfg m [] stream).isOk && (idle cfg outside [] stream).isOk && !(idle cfg inMeta [] stream).isOk &&
      !(idle cfg m [] []).isOk do
    failed := true; IO.println "FAIL: the Idle model's frame probes"
  IO.println "frame: the Idle model ignores a byte outside the arena, and refuses a changed answer index and a wrong stream"
  -- 6. revision 3, change 4: a service with a state word in the arena; the separation; ServiceActive
  match stateWordProbes with
  | .ok lines => for line in lines do IO.println line
  | .error e => failed := true; IO.println s!"FAIL: {e}"
  -- 7. revision 3, change 2: the caller's reference, admitted and not
  match referenceProbes with
  | .ok lines => for line in lines do IO.println line
  | .error e => failed := true; IO.println s!"FAIL: {e}"
  (← IO.getStdout).flush
  for cfg in [({name := "the caller's reference follows the peer being configured",arenaSize := 0x1000+72*40,spacing := 72} : Config),
      {high with name := "the caller's reference follows the peer, kernel-range addresses",arenaSize := 0x1000+72*40,spacing := 72}] do
    match runConfig cfg input 0 [4,6] (moves := true) with
    | .ok out => IO.println s!"closed world: {cfg.name}: holds ({out.insertions} insertions, {out.lookups} lookups, {out.moves} reference steps between calls)"
    | .error e => failed := true; IO.println s!"FAIL: closed world: {cfg.name}: {e}"
    (← IO.getStdout).flush
  if failed then IO.eprintln "FAIL"; return 1
  IO.println "PASS"
  return 0
