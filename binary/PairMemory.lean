import ProbeSupport

/-! Executable index-lookup reconstruction. No definition in this module reads
the expected mirror state while decoding memory. This is one physical component
of World, not a reconstruction of its supplied environment or unrelated state. -/
namespace Binary.Pair
open Leanux Leanux.WG

structure DecodeError where
  path : String
  address : Nat
  detail : String
  deriving Repr, BEq

def DecodeError.message (e : DecodeError) : String :=
  s!"{e.path} at {e.address}: {e.detail}"

abbrev Decode := Except DecodeError

structure Names where
  table : Nat
  peers : List (PeerId × Nat)
  owners : List (IndexOwner × Nat)
  deriving Repr

def disjointRanges (a size b otherSize : Nat) : Bool :=
  a + size ≤ b || b + otherSize ≤ a

/-- Identities and roots are supplied once. Pointer contents are never supplied. -/
def Names.validate (n : Names) (o : Offsets) : Decode Unit := do
  unless o.tableSize == 8192 * o.headSize && o.headSize == 8 && o.first == 0 &&
      o.buckets == 0 && o.entrySize == 32 do
    throw ⟨"layout", n.table, "unsupported index-table layout"⟩
  unless o.peer == Layouts.entry_peer && o.hash == Layouts.entry_index_hash &&
      o.next == Layouts.node_next && o.pprev == Layouts.node_pprev &&
      o.kind == Layouts.entry_type && o.index == Layouts.entry_index &&
      o.peerRefcount == Layouts.peer_refcount && o.keypairEntry == Layouts.keypair_entry &&
      o.peerHandshake + o.handshakeEntry + o.entrySize ≤ Layouts.peerSize do
    throw ⟨"layout", n.table, "field offsets disagree with generated layouts or containing object"⟩
  unless 0 < n.table && n.table + o.tableSize < 2^64 do
    throw ⟨"interpretation.table", n.table, "NULL or wrapping table"⟩
  unless (n.peers.map Prod.fst).eraseDups.length == n.peers.length &&
      (n.peers.map Prod.snd).eraseDups.length == n.peers.length do
    throw ⟨"interpretation.peers", 0, "duplicate identity or address"⟩
  unless (n.owners.map Prod.fst).eraseDups.length == n.owners.length &&
      (n.owners.map Prod.snd).eraseDups.length == n.owners.length do
    throw ⟨"interpretation.owners", 0, "duplicate identity or address"⟩
  for (_, a) in n.peers do
    unless 0 < a && a + Binary.Layouts.peerSize < 2^64 do
      throw ⟨"interpretation.peer", a, "NULL or wrapping allocation"⟩
  for (owner, a) in n.owners do
    unless 0 < a && a + o.entrySize < 2^64 do
      throw ⟨"interpretation.owner", a, "NULL or wrapping entry"⟩
    if let .handshake id := owner then
      let some (_, p) := n.peers.find? (·.1 == id)
        | throw ⟨"interpretation.owner", a, "missing containing peer"⟩
      unless a == p + o.peerHandshake + o.handshakeEntry do
        throw ⟨"interpretation.owner", a, "handshake entry is not embedded in its peer"⟩
  -- Entries embedded in peers deliberately overlap their containing object.
  -- Distinct containing allocations must not overlap one another or the table.
  let allocations := n.peers.map (fun (_, a) => (a, Layouts.peerSize)) ++
    n.owners.filterMap (fun (owner, a) => match owner with
      | .handshake _ => none | .keypair _ => some (a - o.keypairEntry, Layouts.keypairSize))
  for (a, size) in allocations do
    unless a + size < 2^64 && disjointRanges a size n.table o.tableSize do
      throw ⟨"interpretation.separation", a, "wrapping allocation or overlap with table"⟩
  for (allocation, i) in allocations.zipIdx do
    for other in allocations.drop (i+1) do
      unless disjointRanges allocation.1 allocation.2 other.1 other.2 do
        throw ⟨"interpretation.separation", allocation.1, s!"overlapping allocation at {other.1}"⟩

def word (m : DataMem) (path : String) (a bytes : Nat) : Decode Nat :=
  if a + bytes ≤ 2^64 then
    match m.loadBytes (.ofNat 64 a) bytes with
    | some bs => .ok (Int.ofBytes bs).toNat
    | none => .error ⟨path, a, s!"missing {bytes}-byte range"⟩
  else .error ⟨path, a, "wrapping read"⟩

def peerId (n : Names) (path : String) (a : Nat) : Decode (Option PeerId) := do
  if a == 0 then return none
  let some (id, _) := n.peers.find? (·.2 == a)
    | throw ⟨path, a, "unresolved peer pointer"⟩
  return some id

def ownerAt (n : Names) (path : String) (a : Nat) : Decode IndexOwner := do
  let some (id, _) := n.owners.find? (·.2 == a)
    | throw ⟨path, a, "unresolved embedded entry"⟩
  return id

/-- A finite traversal with explicit cycle, backlink and hash checks. Fuel
comes from the registered owner count, not from the source's expected list. -/
def bucket (n : Names) (o : Offsets) (m : DataMem) (b : Nat) :
    Nat → Nat → Nat → List Nat → Decode (List IndexEntry)
  | 0, link, _, _ =>
    if link == 0 then .ok [] else .error ⟨s!"bucket[{b}]", link, "traversal exhausted"⟩
  | fuel + 1, link, previous, seen => do
    if link == 0 then return []
    unless link ≥ o.hash do throw ⟨s!"bucket[{b}]", link, "invalid node address"⟩
    if seen.contains link then throw ⟨s!"bucket[{b}]", link, "cycle"⟩
    let a := link - o.hash
    let owner ← ownerAt n s!"bucket[{b}].owner" a
    let index ← word m s!"bucket[{b}].index" (a + o.index) 4
    unless index % 8192 == b do throw ⟨s!"bucket[{b}].index", a, "wrong bucket"⟩
    let kind ← word m s!"bucket[{b}].kind" (a + o.kind) 4
    let expectedKind := match owner with | .handshake _ => 1 | .keypair _ => 2
    unless kind == expectedKind do throw ⟨s!"bucket[{b}].kind", a, "kind disagrees with containing object"⟩
    let back ← word m s!"bucket[{b}].pprev" (link + o.pprev) 8
    unless back == previous do throw ⟨s!"bucket[{b}].pprev", link + o.pprev, s!"{back} != {previous}"⟩
    let next ← word m s!"bucket[{b}].next" (link + o.next) 8
    let rest ← bucket n o m b fuel next (link + o.next) (link :: seen)
    return {index, owner} :: rest

structure LookupState where
  buckets : Array (List IndexEntry)
  ownerWords : List (IndexOwner × Option PeerId)
  refcounts : List (PeerId × Nat)
  deriving Repr, BEq

/-- Complete table membership/order within each bucket, every registered owner
word and peer count. Cross-bucket list order has no physical representation. -/
def reconstruct (n : Names) (o : Offsets) (m : DataMem) : Decode LookupState := do
  n.validate o
  let mut buckets := #[]
  for b in [:8192] do
    let head := n.table + o.buckets + b * o.headSize + o.first
    let first ← word m s!"bucket[{b}].head" head 8
    buckets := buckets.push (← bucket n o m b (n.owners.length + 1) first head [])
  let ownerWords ← n.owners.mapM fun (owner, a) => do
    let path := s!"owner[{repr owner}].peer"
    let ptr ← word m path (a + o.peer) 8
    return (owner, ← peerId n path ptr)
  let refcounts ← n.peers.mapM fun (id, a) => do
    return (id, ← word m s!"peer[{id}].refcount" (a + o.peerRefcount) 4)
  return {buckets, ownerWords, refcounts}

/-- The fixed source projection. It does not take a candidate interpretation,
and therefore cannot omit a source object just because its mapping is absent. -/
def target (d : Device) : LookupState := Id.run do
  let buckets := (List.range 8192).toArray.map fun b =>
    d.indexTable.filter (fun e => e.index % 8192 == b)
  let ownerWords := (d.peers.toList.map fun (id, p) => (.handshake id, p.handshakeEntryPeer)) ++
    (d.keypairs.toList.map fun (id, k) => (.keypair id, k.peer))
  return {buckets, ownerWords, refcounts := d.peers.toList.map fun (id, p) => (id, p.refcount)}

/-- The assertion itself is the logical relation; there is no separate checker
specification. The operational caller reports its failing component below. -/
def Corresponds (n : Names) (o : Offsets) (m : DataMem) (d : Device) : Prop :=
  reconstruct n o m = .ok (target d)

def compareState (actual expected : LookupState) : Except String Unit := do
  unless actual.buckets.size == expected.buckets.size do throw "table bucket count differs"
  for i in [:actual.buckets.size] do
    unless actual.buckets[i]! == expected.buckets[i]! do
      throw s!"bucket[{i}]: binary={repr actual.buckets[i]!}, mirror={repr expected.buckets[i]!}"
  unless actual.ownerWords == expected.ownerWords do
    throw s!"owner peer words: binary={repr actual.ownerWords}, mirror={repr expected.ownerWords}"
  unless actual.refcounts == expected.refcounts do
    throw s!"peer refcounts: binary={repr actual.refcounts}, mirror={repr expected.refcounts}"

def assertMemory (n : Names) (o : Offsets) (m : DataMem) (w : World) : Except String Unit := do
  let some d := w.k.wg | throw "mirror device missing"
  let actual ← (reconstruct n o m).mapError DecodeError.message
  compareState actual (target d)

end Binary.Pair
