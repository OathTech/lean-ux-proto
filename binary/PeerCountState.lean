import Image
import Memory

namespace Binary.PeerCountPhase
abbrev Address := BitVec 64

/-- The old count observed by the successful machine compare/exchange.
    This is execution history, not a supplied mirror value. -/
structure Pending where
  address : Address
  old : BitVec 32
  deriving DecidableEq

/-- The mirror commits its count at helper return. The successful physical
    CMPXCHG precedes the retry/negative/wrap/dead decisions. Track that one
    outstanding store from its actual edge; RET ends the phase. The history
    used by R must be the history produced by historyStep, starting at lookup
    entry, not a separately supplied sequence. -/
def edge (pending : Option Pending) (before after : MachineState) : Option Pending :=
  if before.pc = Image.PeerGet.entry + 0xaf then none
  else if before.pc = Image.PeerGet.entry + 0x4a ∧
      after.pc = Image.PeerGet.entry + 0x4f ∧ after.data.status.zf then
    some ⟨before.data.regs.r13.toBitVec, before.data.regs.get (.low .rax .W32)⟩
  else pending

def scan : Option Pending → List MachineState → Option Pending
  | pending, [] | pending, [_] => pending
  | pending, before :: after :: rest => scan (edge pending before after) (after :: rest)

/-- Equality to the actual word except at the outstanding increment's
    address. There the old source count is the captured machine operand and
    the current word must be its exact machine-width successor. No positivity
    or overflow bound is baked into this relation. -/
def At (pending : Option Pending) (memory : Mem 64) (address : Address) (count : Nat) : Prop :=
  match pending with
  | none => memory.loadInt address 4 = some (count : Int)
  | some p =>
    if address = p.address then
      count = p.old.toNat ∧ memory.loadInt address 4 = some ((p.old + 1).toNat : Int)
    else memory.loadInt address 4 = some (count : Int)

end Binary.PeerCountPhase
