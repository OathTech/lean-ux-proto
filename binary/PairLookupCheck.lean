import PairLookupNames
import PairIndexCallCheck

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase CommonBitsCoverage

def shapeSpans (n : Names) (o : Offsets) : List Span :=
  (n.table,o.tableSize)::n.owners.map (fun (_,base) => (base+8,24))
def ownerSpans (n : Names) : List Span := n.owners.map fun (_,base) => (base,8)
def countSpans (n : Names) (o : Offsets) : List Span := n.peers.map fun (_,base) => (base+o.peerRefcount,4)

def outputNeeded (v : LookupRelation.View) : Bool :=
  match v.count with | none => false | some count => count != 0 && count+1<2^31

def outputSpan (s : MachineState) : List Span := [(s.data.regs.rcx.toNat,8)]

/-- The same reconstruction as the mutators, followed by present ABI,
callback and allocation checks. Output storage is required only on a live
accepted hit. In this subsystem it belongs to the caller, outside the retained
index heap; the original M1 alias-permitting theorem is unchanged. -/
def callBoundary (n : Names) (o : Offsets) (coverage : Context) (s : MachineState)
    (w : World) (query : Nat) (kinds : List IndexKind) (ra : UInt64) : Except String Unit := do
  Remove.assertAt n o s.data.dmem w
  unless interpretationCheck n do throw "lookup.call.address-interpretation"
  let some d := w.k.wg | throw "lookup.call.missing-device"
  let c := callConfig n w d query kinds
  let v := callView c d
  let mask := s.data.regs.get (.low .rsi .W32)
  unless s.pc==Image.Lookup.entry && s.data.regs.rdi.toBitVec==c.table &&
      (s.data.regs.get (.low .rdx .W32)).toNat==query &&
      decide (mask &&& kindWord .handshake ≠ 0)==kinds.contains .handshake &&
      decide (mask &&& kindWord .keypair ≠ 0)==kinds.contains .keypair do
    throw "lookup.call.arguments"
  Index.callFrameCheck n o coverage s ra (LookupStackWords c)
  unless spansApart (ownerSpans n ++ countSpans n o) (shapeSpans n o) &&
      spansApart (ownerSpans n) (countSpans n o) do throw "lookup.call.data-separation"
  if outputNeeded v then
    unless (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome do throw "lookup.call.output-mapping"
    unless spansApart (outputSpan s) (Index.storageSpans n o ++
        Index.callStack s (LookupStackWords c) true ++ Trie.callServices coverage) do
      throw "lookup.call.output-separation"

def Pre (n : Names) (o : Offsets) (coverage : Context) (s : MachineState)
    (w : World) (query : Nat) (kinds : List IndexKind) (ra : UInt64) : Prop :=
  callBoundary n o coverage s w query kinds ra=.ok ()

end Binary.Pair.IndexLookup
