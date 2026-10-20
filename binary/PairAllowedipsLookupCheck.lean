import PairAllowedipsReadSet
import PairAllowedips

namespace Binary.Pair.Allowedips
open Leanux

def lookupWrites (names : Names) (o : AllowedipsProbe.Offsets)
    (c : CommonBitsCoverage.Context) (s : MachineState) : List Span :=
  (Trie.callStack s false ++ Trie.callBuffers c ++ [(TrustBase.preemptCountAddress.toNat,4)]) ++
    Trie.countSpans names.trie o

/-- The extended entry check. The additional condition is a physical frame
separation, independent of the target values. The root comes from the table
that the shared reconstruction checks, rather than an unrelated supplied root. -/
def lookupBoundary (names : Names) (input : AllowedipsProbe.Input)
    (coverage : CommonBitsCoverage.Context) (initial : MachineState) (w : World)
    (family key : Nat) (ra : UInt64) : Except String Unit := do
  assertAt names input.offsets initial.data.dmem w
  let some d := w.wg.dev | throw "allowedips.lookup.device"
  unless family == 4 || family == 6 do throw "allowedips.lookup.family"
  let root := if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
  let width := if family == 4 then 32 else 128
  unless spansApart (metadataSpans names input.offsets) (lookupWrites names input.offsets coverage initial) do
    throw "allowedips.lookup.metadata-separation"
  Trie.callBoundary names.trie input coverage initial w root width key ra

end Binary.Pair.Allowedips
