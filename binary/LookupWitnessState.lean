import LookupProjection
import TrustBase

/-! Concrete read projection of operation 3 of the recorded
    d1_wrong_receiver_index_same_bucket prefix. Addresses are the probe's
    synthetic materialization, not captured kernel pointers. Unread heap
    bytes are deliberately absent; neither their absence nor their value
    is an entry-domain requirement. -/
namespace Binary.LookupWitness
open Leanux Leanux.WG TrustBase

def entry : IndexEntry := ⟨0x0a0b0c0d, .handshake 0⟩
def device : Device := {ifindex := 3, ifname := "wg0", indexTable := [entry]}

/-- Unobserved World components are arbitrary concrete inhabitants. No
    physical representation of these components is asserted. -/
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

def config : LookupRelation.Config := {
  table := 0x100000, query := 0x8a0b0c0d, kinds := [.handshake]
  peers := fun id => .ofNat 64 (0x600000 + 0x1000 * id)
  keypairs := fun id => .ofNat 64 (0x700000 + 0x1000 * id)
  focus := ⟨none, none⟩, incomingSteps := [], rxSection := world.netRxSection }

def view : LookupRelation.View := ⟨[entry], none, none⟩

def coverage : KcovLayout := {
  task := 0x800000, area := 0x900000, capacity := 1024, mode := 2, softirqEnabled := 0 }

def memory : Mem 64 :=
  let m : Mem 64 := (List.replicate 0x810 (0 : UInt8)).At (0x400000#64)
  let m := m.storeBytes 0x900000 (List.replicate 8192 0)
  let m := m.storeInt 0x400800 8 0x500000
  let m := m.storeInt 0x106068 8 0x6000e8
  let m := m.storeInt 0x6000e8 8 0
  let m := m.storeInt 0x6000f8 4 1
  let m := m.storeInt 0x6000fc 4 0x0a0b0c0d
  let m := m.storeInt preemptCountAddress 4 0
  let m := m.storeInt currentTaskAddress 8 0x800000
  let m := m.storeInt softirqPendingAddress 2 0
  let m := m.storeInt 0x8006e0 4 2
  let m := m.storeInt 0x8006e4 4 1024
  let m := m.storeInt 0x8006e8 8 0x900000
  m.storeInt 0x800704 4 0

def data : MachineData := {dmem := memory, regs := {
  rdi := 0x100000, rsi := 1, rdx := 0x8a0b0c0d, rcx := 0x300000,
  rsp := 0x400800, rbx := 0x11, rbp := 0x22, r12 := 0x33,
  r13 := 0x44, r14 := 0x55, r15 := 0x66}}

def initial : MachineState := ⟨data, Image.Lookup.entry⟩

end Binary.LookupWitness
