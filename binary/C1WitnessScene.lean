import C1WitnessStub

/-! Result C1, open proposition `WitnessHolds`: the concrete layout, memory,
mirror world and entry states of the witness. Definitions only.

One base memory serves every entry state: a mapped stack with the return
word (and, further down, the return word of the service's own entry state), the coverage metadata and an empty coverage buffer in PC mode (so the
context `c` is `Needed`), an empty table with two registered peers, the
`node_cache` word, four address buffers, and package 4's allocator bytes
with five pending outcomes. A later entry state takes its heap bytes from
the previous call's final memory and every other byte from the base
(`over`): the bytes outside the heap are the caller's to choose. -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

/-! ## A memory given by a list of stores, and its bytes as a list function -/

/-- Little-endian bytes of `v`. -/
def le (n v : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (v / 256^i % 256)

/-- The memory holding these stores; the head of the list is the latest. -/
def build : List (Nat × List UInt8) → Mem 64
  | [] => {}
  | (a,bytes) :: rest => (build rest).storeBytes (.ofNat 64 a) bytes

/-- The byte `build` holds at `x`, without a memory. -/
def lookup : List (Nat × List UInt8) → Nat → Option UInt8
  | [], _ => none
  | (a,bytes) :: rest, x => if a ≤ x ∧ x < a + bytes.length then bytes[x - a]? else lookup rest x

/-! ## The layout -/

def tableAt : Nat := 0x100000
def peers : List (PeerId × Nat) := [(0,0x600000),(1,0x601000)]
def L : Layout := Stub.layout tableAt peers
def stack : Nat := 0x400800
/-- Every call of `Executed` returns here (an address outside every listing). -/
def ra : UInt64 := 0xffffffff82000000
/-- The service's own entry state is a call from allowedips.c:190: its return
word is that site's return address, 64 bytes down the same stack. -/
def site : UInt64 := 0xffffffff813a0ff2
def serviceStack : Nat := stack - 64
def task : Nat := 0x800000
def area : Nat := 0x900000
def capacity : Nat := 64
/-- PC-mode coverage with room for records: the buffer is in use. -/
def c : Context := ⟨⟨.ofNat 64 task,.ofNat 64 area,.ofNat 32 capacity,2,0⟩,512⟩
def keyAt (i : Nat) : Nat := 0xb00000 + 16*i

/-- The five pending answers of `Executed`. -/
def five : List HiddenRecord :=
  [outcome 77 true, outcome 78 true, outcome 79 true, outcome 78 true, outcome 79 false]

def peerSpans (a : Nat) : List (Nat × List UInt8) :=
  [(a+AllowedipsMutationLayout.allowedips_list,le 8 (a+AllowedipsMutationLayout.allowedips_list)),
   (a+AllowedipsMutationLayout.allowedips_list+8,le 8 (a+AllowedipsMutationLayout.allowedips_list)),
   (a+Root.nodeOffsets.peerRefcount,le 4 1),
   (a,List.replicate Layouts.peerSize 0)]

/-- Everything but the allocator's bytes. -/
def preSpans : List (Nat × List UInt8) :=
  [(stack,le 8 ra.toNat),
   (serviceStack,le 8 site.toNat),
   (stack-0x800,List.replicate 0x1000 0),
   (preemptCountAddress.toNat,le 4 512),
   (currentTaskAddress.toNat,le 8 task),
   (softirqPendingAddress.toNat,le 2 0),
   (task+0x6e0,le 4 2),
   (task+0x6e4,le 4 capacity),
   (task+0x6e8,le 8 area),
   (task+0x704,le 4 0),
   (area,List.replicate (8*capacity) 0),
   (tableAt,List.replicate AllowedipsMutationLayout.tableSize 0)] ++
  peerSpans 0x600000 ++ peerSpans 0x601000 ++
  [(cacheWord,le 8 Stub.state),
   (keyAt 0,[10,0,0,0]),(keyAt 1,[11,0,0,1]),(keyAt 2,[12,0,0,1]),(keyAt 3,[10,0,0,5])]

/-- The base memory: package 4's allocator bytes installed over the rest. -/
def base : Mem 64 := Stub.install (build preSpans) five

/-- The same memory as one list of stores. -/
def baseSpans : List (Nat × List UInt8) :=
  [(Stub.objects,List.replicate (128*Stub.slots) 0),(Stub.table,five.map Stub.outcomeByte),(Stub.state,[0])] ++
    preSpans

/-- Whether `x` is a heap byte of the layout. -/
def heapAt (x : Nat) : Bool := L.heap.any fun (a,n) => a ≤ x && x < a+n

/-- The heap bytes of `m` over the base memory. -/
def over (m : Mem 64) : Mem 64 :=
  (base.filter fun a _ => !heapAt a.toNat) ∪ (m.filter fun a _ => heapAt a.toNat)

/-! ## The mirror's world -/

def world : World :=
  let peers := (List.range 2).foldl (fun peers id => peers.insert id {
    remoteStatic := List.replicate 32 0,presharedKey := List.replicate 32 0,
    precomputedStaticStatic := List.replicate 32 0,internalId := id,refcount := 1})
    ({} : Std.TreeMap PeerId Peer)
  let dev : Device := {
    ifindex := 1,ifname := "wg0",peers,nextNode := 0,
    peerAllowedips := {seq := 0}}
  let ambient : Ambient := {
    env := Runner.harnessEnv,timing := Env.timing,hidden := some five,
    allocArmed := ["allocNode190","allocNode205","allocNode234"]}
  {ambient,tasks := Runner.initialTasks 1024 false false false,fs := {},wg := {dev := some dev}}

/-! ## Entry states -/

def flags : SystemFlags := {bits := 0}

/-- `wg_allowedips_insert_v4(table, keyAt i, length, peerAt)` on memory `m`. -/
def insertRegs (i length peerAt : Nat) : Reg64s :=
  {rdi := .ofNat tableAt, rsi := .ofNat (keyAt i), rdx := .ofNat length, rcx := .ofNat peerAt, rsp := .ofNat stack}

def insertEntry (m : Mem 64) (i length peerAt : Nat) : MachineState :=
  ⟨{regs := insertRegs i length peerAt, dmem := m, system := flags},AllowedipsMutationImage.Insert4.entry⟩

/-- `lookup(root, 32, keyAt 3)` on memory `m`. -/
def lookupEntry (m : Mem 64) (root : Nat) : MachineState :=
  ⟨{regs := {rdi := .ofNat root,rsi := 32,rdx := .ofNat (keyAt 3),rsp := .ofNat stack},dmem := m,
    system := flags},AllowedipsImage.Lookup.entry⟩

/-- The service's own entry state: `kmem_cache_zalloc(node_cache, GFP_KERNEL)`
called from allowedips.c:190 on the base memory. -/
def serviceEntry : MachineState :=
  ⟨{regs := {rdi := .ofNat Stub.state,rsi := 0xdc0,rsp := .ofNat serviceStack},dmem := base,system := flags},
    allocEntry⟩

end Binary.Statements.C1.Witness
