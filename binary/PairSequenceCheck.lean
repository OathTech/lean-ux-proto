import PairIndexChecked
import PairReplace

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage

inductive Call where
  | lookup (query : Nat) (kinds : List IndexKind)
  | remove (owner : IndexOwner)
  | replace (peer : PeerId) (keypair : KeypairId)
  deriving Repr

inductive Answer where
  | lookup (value : Option (IndexOwner×PeerId))
  | remove
  | replace (value : Bool)
  deriving Repr, BEq

def source : Call → M Answer
  | .lookup q kinds => return .lookup (← WG.indexLookup kinds q)
  | .remove owner => do WG.indexRemove owner; return .remove
  | .replace pid kid => return .replace (← WG.indexReplaceHandshake pid kid)

def program : List Call → M (List Answer)
  | [] => pure []
  | call::rest => do return (← source call)::(← program rest)

def stackSizes : List Nat := [4,5,6,13]
def ownerKind : IndexOwner → Nat | .handshake _ => 1 | .keypair _ => 2

/-- Check the initially allocated fields which a later successful replacement
may read, even when its new owner is currently unlinked. -/
def residentCheck (n : Names) (o : Offsets) (m : DataMem) : Except String Unit := do
  let _ ← n.owners.mapM fun (owner,base) => do
    let kind ← (word m "sequence.kind" (base+o.kind) 4).mapError DecodeError.message
    unless kind==ownerKind owner do throw "sequence.owner-kind"
    let _ ← (word m "sequence.next" (base+o.hash+o.next) 8).mapError DecodeError.message
    let _ ← (word m "sequence.index" (base+o.index) 4).mapError DecodeError.message
    pure ()
  pure ()

/-- One initial resource check. No future entry, binary execution or mirror
result is an input. The finite stack sizes are those of the three anchors. -/
def initialCheck (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (w : World) (ra : UInt64) : Except String Unit := do
  Remove.assertAt n o base.data.dmem w
  unless IndexLookup.interpretationCheck n do throw "sequence.interpretation"
  let _ ← stackSizes.mapM (Index.callFrameCheck n o c base ra)
  residentCheck n o base.data.dmem
  unless spansApart (IndexLookup.ownerSpans n ++ IndexLookup.countSpans n o) (IndexLookup.shapeSpans n o) &&
      spansApart (IndexLookup.ownerSpans n) (IndexLookup.countSpans n o) do throw "sequence.data-separation"
  unless (base.data.dmem.loadInt base.data.regs.rcx.toBitVec 8).isSome do throw "sequence.output-mapping"
  unless stackSizes.all (fun words => spansApart (IndexLookup.outputSpan base)
      (Index.storageSpans n o ++ Index.callStack base words true ++ Trie.callServices c)) do
    throw "sequence.output-separation"
  unless spansApart (Trie.callServices c) (Index.callStack base 13 true) do
    throw "sequence.caller-return-separation"

/-- ABI installation is explicit and writes just the caller's return slot.
The shared heap and immutable allocation interpretation are retained. -/
def install (n : Names) (base : MachineState) (ra : UInt64) (pc : Int64)
    (arg2 arg3 : Nat) (current : MachineState) : MachineState :=
  ⟨{current.data with
      regs := {current.data.regs with
        rdi := .ofNat n.table, rsi := .ofNat arg2, rdx := .ofNat arg3,
        rcx := base.data.regs.rcx, rsp := base.data.regs.rsp},
      dmem := current.data.dmem.storeInt base.data.regs.rsp.toBitVec 8 ra.toBitVec.toInt},pc⟩

def prepare (n : Names) (base : MachineState) (ra : UInt64) (call : Call)
    (current : MachineState) : Except String MachineState := do
  match call with
  | .lookup query kinds => return install n base ra Image.Lookup.entry (kindMask kinds) query current
  | .remove owner => return install n base ra (.ofNat Remove.entry) (← addressOf n owner) 0 current
  | .replace pid kid =>
    let old ← addressOf n (.handshake pid)
    let new ← addressOf n (.keypair kid)
    return install n base ra (.ofNat Replace.entry) old new current

/-- Source-only per-call obligations. Freshness is conditional on successful
replacement, exactly as in the individual theorem. -/
def Admissible (n : Names) (call : Call) (w : World) : Prop :=
  match call with
  | .lookup query _ => query<2^32
  | .remove owner => ∃ a, addressOf n owner=.ok a
  | .replace pid kid =>
      (∃ a, addressOf n (.handshake pid)=.ok a) ∧
      (∃ a, addressOf n (.keypair kid)=.ok a) ∧
      ∀ d, w.k.wg=some d → d.indexTable.any (·.owner==.handshake pid)=true →
        d.indexTable.any (·.owner==.keypair kid)=false

end Binary.Pair.Sequence
