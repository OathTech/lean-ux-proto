import AllowedipsSource
import AllowedipsImage
import AllowedipsLayout
import TrustBase

/-! Concrete source-read projection for `b1_trie_routing`, operations 5 and 8.
The nodes and counts are reproduced by `binary/allowedips_probe.py`; both
recorded prefixes have the same projection. Parent/list fields and unrelated
World fields below are arbitrary concrete inhabitants, not captured data.
Synthetic addresses, stack and the nested-BH count 512 match the runnable
probe. This module declares no entry precondition and proves no binary run. -/
namespace Binary.AllowedipsWitness
open Leanux Leanux.WG TrustBase
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure NodeFixture where
  id : NodeId
  peer : Option PeerId
  child0 : Option NodeId
  child1 : Option NodeId
  cidr : Nat
  width : Nat
  key : Nat

def NodeFixture.node (n : NodeFixture) : AipNode :=
  {peer := n.peer, bit := #[n.child0,n.child1], cidr := n.cidr,
   bitlen := n.width, bits := n.key, parent := .root4}

def fixtures : List NodeFixture := [
  ⟨0, some 0, some 2, none, 8, 32, 0xa000000⟩,
  ⟨1, some 0, some 9, none, 8, 128, 0xfd000000000000000000000000000000⟩,
  ⟨2, some 1, some 4, none, 16, 32, 0xa010000⟩,
  ⟨3, some 1, none, none, 32, 128, 0xfd000001000000000000000000000000⟩,
  ⟨4, some 2, some 5, none, 24, 32, 0xa010200⟩,
  ⟨5, some 3, none, none, 32, 32, 0xa010203⟩,
  ⟨6, some 3, none, none, 16, 32, 0xc0a80000⟩,
  ⟨7, none, some 0, some 6, 0, 32, 0xc0a80000⟩,
  ⟨8, some 4, none, none, 32, 128, 0xfd000002000000000000000000000000⟩,
  ⟨9, none, some 3, some 8, 30, 128, 0xfd000002000000000000000000000000⟩
 ]

def nodeRows : List (NodeId × AipNode) := fixtures.map fun n => (n.id,n.node)

def peer (id : PeerId) : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
  internalId := id, refcount := 1 }

def device : Device := {
  ifindex := 3, ifname := "wg0",
  peerAllowedips := {root4 := some 7, root6 := some 1},
  nodes := nodeRows.foldl (fun nodes row => nodes.insert row.1 row.2) {},
  peers := (List.range 5).foldl (fun peers id => peers.insert id (peer id)) {} }

def world : World := {
  k := {
    task := {
      files := {
        count := 1, resizeInProgress := false, nextFd := 0
        fdt := {maxFds := 0, fd := #[], openFds := #[], closeOnExec := #[]} }
      rlimitNofile := 0 }
    files := {}, nextFile := 0, ctxs := {}, nextCtx := 0, idaUsed := {},
    nrFiles := 0, maxFiles := 0, anonInodeInodeErr := false, wg := some device }
  env := fun _ _ => false
  timing := {advanceWait := 0, traceBound := 0} }

def key4 : Nat := 0x0a010203
def key6 : Nat := 0xfd000002000000000000000000000009

def nodeAddress (id : NodeId) : BitVec 64 := .ofNat 64 (0xa00000 + id*0x1000)
def peerAddress (id : PeerId) : BitVec 64 := .ofNat 64 (0x600000 + id*0x1000)
def keyAddress : BitVec 64 := 0xb00000

def coverage : KcovLayout := {
  task := 0x800000, area := 0x900000, capacity := 1024, mode := 2, softirqEnabled := 0 }

def nodeMemory (memory : Mem 64) (row : NodeFixture) : Mem 64 :=
  let a := nodeAddress row.id
  let n := row.node
  let memory := memory.storeBytes a (List.replicate AllowedipsLayout.nodeSize 0)
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.peer) 8
    (n.peer.map (fun pid => (peerAddress pid).toNat) |>.getD 0)
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.bit) 8
    (row.child0.map (fun id => (nodeAddress id).toNat) |>.getD 0)
  let memory := memory.storeInt (a + .ofNat 64 (AllowedipsLayout.bit+8)) 8
    (row.child1.map (fun id => (nodeAddress id).toNat) |>.getD 0)
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.cidr) 1 n.cidr
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.bit_at_a) 1
    (n.cidr/8 ^^^ ((n.bitlen/8-1)%8))
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.bit_at_b) 1 (7-n.cidr%8)
  let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.bitlen) 1 n.bitlen
  if n.bitlen = 32 then
    memory.storeInt (a + .ofNat 64 AllowedipsLayout.bits) 4 n.bits
  else
    let memory := memory.storeInt (a + .ofNat 64 AllowedipsLayout.bits) 8 (n.bits / 2^64)
    memory.storeInt (a + .ofNat 64 (AllowedipsLayout.bits+8)) 8 (n.bits % 2^64)

def memory (width key : Nat) : Mem 64 :=
  let m : Mem 64 := (List.replicate 0x810 (0 : UInt8)).At (0x400000#64)
  let m := m.storeInt 0x400800 8 0x500000
  let m := m.storeInt preemptCountAddress 4 512
  let network := (List.range (width/8)).map fun i => UInt8.ofNat (key / 256^(width/8-1-i) % 256)
  let m := m.storeBytes keyAddress network
  let m := fixtures.foldl nodeMemory m
  let m := (List.range 5).foldl (fun m pid =>
    m.storeInt (peerAddress pid + .ofNat 64 Layouts.peer_refcount) 4 1) m
  let m := m.storeInt currentTaskAddress 8 0x800000
  let m := m.storeInt softirqPendingAddress 2 0
  let m := m.storeInt 0x8006e0 4 2
  let m := m.storeInt 0x8006e4 4 1024
  let m := m.storeInt 0x8006e8 8 0x900000
  let m := m.storeInt 0x800704 4 0
  m.storeBytes 0x900000 (List.replicate 8192 0)

def initial (root width key : Nat) : MachineState :=
  ⟨{dmem := memory width key, regs := {
    rdi := .ofNat (nodeAddress root).toNat, rsi := .ofNat width,
    rdx := .ofNat keyAddress.toNat, rsp := 0x400800,
    rbx := 0x11, rbp := 0x22, r12 := 0x33, r13 := 0x44, r14 := 0x55, r15 := 0x66}},
    AllowedipsImage.Lookup.entry⟩

def initial4 : MachineState := initial 7 32 key4
def initial6 : MachineState := initial 1 128 key6

/-- Kernel-reduced source acceptance on the concrete projected trie. -/
theorem source4_result :
    ((WG.lookup (some 7) 32 key4).run world).toOption.map Prod.fst = some (some 3) := by
  unfold WG.lookup WG.findNode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  decide

theorem source6_result :
    ((WG.lookup (some 1) 128 key6).run world).toOption.map Prod.fst = some (some 4) := by
  unfold WG.lookup WG.findNode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  decide

private theorem accepted_of_result (action : M (Option PeerId)) (pid : PeerId)
    (result : (action.run world).toOption.map Prod.fst = some (some pid)) :
    ∃ final, action.run world = .ok (some pid,final) := by
  cases actual : action.run world with
  | error e =>
    rw [actual] at result
    change none = some (some pid) at result
    contradiction
  | ok value =>
    obtain ⟨answer,final⟩ := value
    rw [actual] at result
    change some answer = some (some pid) at result
    have equal : answer = some pid := Option.some.inj result
    subst answer
    exact ⟨final,rfl⟩

theorem source4_accepted :
    ∃ final, (WG.lookup (some 7) 32 key4).run world = .ok (some 3,final) :=
  accepted_of_result _ 3 source4_result

theorem source6_accepted :
    ∃ final, (WG.lookup (some 1) 128 key6).run world = .ok (some 4,final) :=
  accepted_of_result _ 4 source6_result

theorem source4_logged : ∃ final points,
    ((AllowedipsSource.lookup (some 7) 32 key4).run []).run world =
      .ok ((some 3,points),final) := by
  obtain ⟨final,run⟩ := source4_accepted
  obtain ⟨points,logged⟩ := AllowedipsSource.lookup_accepted (some 7) 32 key4 [] world final (some 3) run
  exact ⟨final,points,logged⟩

theorem source6_logged : ∃ final points,
    ((AllowedipsSource.lookup (some 1) 128 key6).run []).run world =
      .ok ((some 4,points),final) := by
  obtain ⟨final,run⟩ := source6_accepted
  obtain ⟨points,logged⟩ := AllowedipsSource.lookup_accepted (some 1) 128 key6 [] world final (some 4) run
  exact ⟨final,points,logged⟩

theorem initial4_arguments : initial4.pc = AllowedipsImage.Lookup.entry ∧
    initial4.data.regs.rdi.toBitVec = nodeAddress 7 ∧ initial4.data.regs.rsi = 32 ∧
    initial4.data.regs.rdx.toBitVec = keyAddress ∧ initial4.data.regs.rsp = 0x400800 := by decide

theorem initial6_arguments : initial6.pc = AllowedipsImage.Lookup.entry ∧
    initial6.data.regs.rdi.toBitVec = nodeAddress 1 ∧ initial6.data.regs.rsi = 128 ∧
    initial6.data.regs.rdx.toBitVec = keyAddress ∧ initial6.data.regs.rsp = 0x400800 := by decide

#print axioms source4_result
#print axioms source6_result
#print axioms source4_logged
#print axioms source6_logged
end Binary.AllowedipsWitness
