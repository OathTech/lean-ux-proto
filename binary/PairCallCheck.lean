import PairLoopCheck
import PairTrieFrame
import AllowedipsWords

namespace Binary.Pair.Trie
open TrustBase CommonBitsCoverage

instance (old : BitVec 32) : Decidable (LookupPendingRead old) := by
  unfold LookupPendingRead
  infer_instance

def callMetadata (c : Context) : List Span :=
  metadataSpans c ++ metadataSpans ⟨c.coverage,c.preempt+512⟩ ++
    (if LookupPendingRead c.preempt then [(softirqPendingAddress.toNat,2)] else [])

def callHeaders (c : Context) : List Span :=
  if c.Needed ∨ (Context.mk c.coverage (c.preempt+512)).Needed then [(c.coverage.area.toNat,8)] else []

def callBuffers (c : Context) : List Span :=
  writeSpans c ++ writeSpans ⟨c.coverage,c.preempt+512⟩

def callServices (c : Context) : List Span :=
  readSpans c ++ readSpans ⟨c.coverage,c.preempt+512⟩ ++
    (if LookupPendingRead c.preempt then [(softirqPendingAddress.toNat,2)] else [])

def trieSpans (names : Names) (o : AllowedipsProbe.Offsets) : List Span :=
  names.nodes.flatMap fun (_,base) => (nodeSpans o).map fun (offset,size) => (base+offset,size)

def countSpans (names : Names) (o : AllowedipsProbe.Offsets) : List Span :=
  names.peers.map fun (_,a) => (a+o.peerRefcount,4)

def callStack (s : MachineState) (returnWord : Bool) : List Span :=
  [((s.data.regs.rsp.toBitVec-144).toNat, if returnWord then 152 else 144)]

/-- Exact network-order decoding expressed with the same byte swap as the
instruction lemma. Missing memory is a rejection, never a default word. -/
def networkKeyCheck (m : DataMem) (base : BitVec 64) (bits key : Nat) : Bool :=
  if bits == 32 then
    match load32 m base with
    | none => false
    | some word => (Allowedips.swap32 word).toNat == key
  else
    match load64 m base, load64 m (base+8) with
    | some high, some low => (Allowedips.swap64 high).toNat*2^64+(Allowedips.swap64 low).toNat == key
    | _, _ => false

/-- Complete-call physical readiness. The 144-byte scratch footprint includes
the two peer-get words deeper than common_bits; the live frame includes RET.
These are byte/state checks, not claims about future callback behavior. -/
def callFrameCheck (names : Names) (o : AllowedipsProbe.Offsets)
    (c : Context) (s : MachineState) (ra : UInt64) (bits key : Nat) : Except String Unit := do
  unless s.data.regs.rsp.toNat % 8 == 0 &&
      s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int) do
    throw "call.abi-return"
  unless (List.range 18).all (fun i =>
      (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome) do
    throw "call.stack-mapping"
  unless networkKeyCheck s.data.dmem s.data.regs.rdx.toBitVec bits key do
    throw "call.network-query"
  unless coverageCheck c s.data.dmem &&
      coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem do
    throw "call.coverage-phases"
  unless (c.preempt+512) &&& 0x000f0000 == 0 do throw "call.hardirq"
  unless (if LookupPendingRead c.preempt then s.data.dmem.loadInt softirqPendingAddress 2 == some 0 else true) do
    throw "call.pending-softirq"
  let preempt := [(preemptCountAddress.toNat,4)]
  unless spansApart (decoderSpans names o) (callStack s false ++ callBuffers c ++ preempt) do
    throw "call.decoder-separation"
  unless spansApart [(s.data.regs.rdx.toNat,if bits == 32 then 4 else 16)]
      (callStack s false ++ writeSpans c) do throw "call.query-separation"
  unless spansApart (callServices c) (callStack s false) do throw "call.service-stack"
  unless spansApart (callBuffers c) (callStack s true ++ callMetadata c ++ preempt) do
    throw "call.buffer-separation"
  unless spansApart (countSpans names o) (callStack s true ++ callServices c ++ trieSpans names o) do
    throw "call.count-separation"
  unless spansApart (callStack s true ++ callMetadata c ++ callHeaders c) preempt do
    throw "call.preempt-separation"

end Binary.Pair.Trie
