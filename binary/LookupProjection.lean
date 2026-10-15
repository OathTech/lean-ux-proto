import PeerCountState
import LookupObservation
import Representation
import OwnerWord

namespace Binary.LookupRelation
open Leanux Leanux.WG

/-- Identities fixed by the entry's first index match, kind test and owner
    word. They are not copies of the entry's peer or device state. Keeping
    the peer identity after NULL store-back retains the dead-count equation. -/
structure Focus where
  owner : Option IndexOwner
  peer : Option PeerId

structure Config where
  table : Address
  query : Nat
  kinds : List IndexKind
  peers : PeerId → Address
  keypairs : KeypairId → Address
  focus : Focus
  incomingSteps : List Step
  rxSection : Nat

/-- Only lookup's WireGuard read/write projection. The head/next/index/type
    fields implement the bucket walk, the owner word supplies and receives
    peer-get's result, and peer-get reads/increments the focused count.
    Unchanged fields are handled by physical and source frame theorems;
    they are not extra clauses of this projection. -/
structure View where
  bucket : List IndexEntry
  ownerWord : Option (Option PeerId)
  count : Option Nat

def project (c : Config) (w : World) : Option View := do
  let d ← w.k.wg
  pure {
    bucket := d.indexTable.filter (fun e => e.index % 8192 == c.query % 8192)
    ownerWord := c.focus.owner.bind (OwnerWord.value d)
    count := c.focus.peer.bind (fun id => (d.peers.get? id).map (·.refcount)) }

/-- A wrong-kind first index match stops the lookup. It does not permit
    searching onward for a different entry of an accepted kind. -/
def selected (c : Config) (es : List IndexEntry) : Option IndexOwner :=
  (es.find? (fun e => e.index == c.query)).bind fun e =>
    if c.kinds.contains e.kind then some e.owner else none

def ownerAddress (c : Config) (o : IndexOwner) : Address :=
  OwnerWord.address c.peers c.keypairs o

def lastHelperReturn (seen : List LookupObservation.Point) : Option MachineState := do
  let p ← seen.getLast?
  match p.tag with
  | .returned name =>
      if name == "wg_peer_get_maybe_zero" then some p.machine else none
  | _ => none

/-- Both control and observed call phase matter: an outer RET may itself
    target a PC in this range, which is not a pending owner store. -/
def ownerPending (seen : List LookupObservation.Point)
    (s : MachineState) : Option MachineState :=
  if s.pc = Image.Lookup.entry+0xbd ∨ s.pc = Image.Lookup.entry+0xc0 ∨
      s.pc = Image.Lookup.entry+0xc3 then lastHelperReturn seen else none

def OwnerFieldAt (c : Config) (seen : List LookupObservation.Point)
    (s : MachineState) (o : IndexOwner) (word : Option PeerId) : Prop :=
  match ownerPending seen s with
  | none => OwnerWord.Field c.peers s.data.dmem (ownerAddress c o) word
  | some snapshot =>
      snapshot.pc = Image.Lookup.entry+0xba ∧
      snapshot.data.regs.rbx.toBitVec = ownerAddress c o ∧
      OwnerWord.Field c.peers snapshot.data.dmem (ownerAddress c o) word ∧
      s.data.dmem.loadInt (ownerAddress c o) 8 =
        some (snapshot.data.regs.rax.toNat : Int)

def helperTag (active : Bool) (point : LookupObservation.Point) : Bool :=
  match point.tag with
  | .call name => if name == "wg_peer_get_maybe_zero" then true else active
  | .returned name => if name == "wg_peer_get_maybe_zero" then false else active
  | _ => active

def helperActive (seen : List LookupObservation.Point) : Bool :=
  seen.foldl helperTag false

/-- Only an actual active helper call uses the pending CMPXCHG phase. The
    operand still comes from the raw execution, never a source-supplied
    count. At helper return the source has committed and ordinary equality
    applies. This leaves unrelated bucket histories out of phase reasoning. -/
def countPhase (raw : List MachineState) (seen : List LookupObservation.Point) :
    Option PeerCountPhase.Pending :=
  if helperActive seen then PeerCountPhase.scan none raw else none

def Physical (c : Config) (raw : List MachineState)
    (seen : List LookupObservation.Point) (s : MachineState) (v : View) : Prop :=
  selected c v.bucket = c.focus.owner ∧
  (∃ head : Address,
    s.data.dmem.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 =
      some (head.toNat : Int) ∧
    BucketShape s.data.dmem head
      (v.bucket.map fun e => (ownerAddress c e.owner, e))) ∧
  (match c.focus.owner with
   | none => v.ownerWord = none
   | some owner => ∃ word,
       v.ownerWord = some word ∧ OwnerFieldAt c seen s owner word) ∧
  (match c.focus.peer with
   | none => v.count = none
   | some pid => ∃ count,
       v.count = some count ∧ c.peers pid ≠ 0 ∧
       PeerCountPhase.At (countPhase raw seen) s.data.dmem
         (c.peers pid + .ofNat 64 Layouts.peer_refcount) count)

/-- Entry-only agreement: later owner store-back can clear its word without
    changing the fixed identity whose count is being simulated. No count
    bound or positivity restriction is imposed here. -/
def EntryFocus (c : Config) (v : View) : Prop :=
  selected c v.bucket = c.focus.owner ∧
  match c.focus.owner with
  | none => c.focus.peer = none
  | some _ => v.ownerWord = some c.focus.peer

def StepsAt (c : Config) (seen : List LookupObservation.Point) (w : World) : Prop :=
  w.steps.toList = c.incomingSteps ++ seen.filterMap (·.step) ∧
  w.netRxSection = c.rxSection

/-- Lookup component of the framed WG simulation, not a claim of adequacy.
    Callers must bind raw/seen to ExecutedCorrespondence's actual prefixes.
    Callback metadata/ABI are execution invariants, not extra World fields.
    A generic frame extension is needed for untouched WG observations. -/
def R (c : Config) (raw : List MachineState)
    (seen : List LookupObservation.Point) (s : MachineState) (w : World) : Prop :=
  raw.getLast? = some s ∧
  (∃ v, project c w = some v ∧ Physical c raw seen s v) ∧
  StepsAt c seen w

/-- Precisely the uniform selected-bucket fields and focused words used by
    this relation. No pprev, other bucket or device-table-pointer field is
    present. BucketShape is a uniform chain representation, not a claim to
    the minimum individual bytes read on an early-hit execution. -/
def Reads (c : Config) (v : View) (address : Address) : Prop :=
  InRange (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 address ∨
  (∃ e ∈ v.bucket, BucketShapeReads (ownerAddress c e.owner) address) ∨
  (∃ owner, c.focus.owner = some owner ∧ InRange (ownerAddress c owner) 8 address) ∨
  (∃ pid, c.focus.peer = some pid ∧
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 address)

end Binary.LookupRelation
