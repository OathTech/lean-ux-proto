import Leanux.Proofs.WG.Index.ReleaseModel

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

inductive ClearSlot where
  | next | previous | current
  deriving DecidableEq, Repr

def ClearSlot.read : ClearSlot → Peer → Option KeypairId
  | .next, p => p.keypairNext
  | .previous, p => p.keypairPrevious
  | .current, p => p.keypairCurrent

def ClearSlot.clear : ClearSlot → Peer → Peer
  | .next, p => { p with keypairNext := none }
  | .previous, p => { p with keypairPrevious := none }
  | .current, p => { p with keypairCurrent := none }

def clearWrite (d : Device) (pid : PeerId) (slot : ClearSlot) (p : Peer) : Device :=
  { d with peers := d.peers.insert pid (slot.clear p) }

/-- The NULL put or the actual immediate-unhash release, including both
unhashes and the decrement/erase order on the last reference. -/
inductive ClearPut : Option KeypairId → Device → Device → Prop
  | null (d : Device) : ClearPut none d d
  | present (d : Device) (id : KeypairId) (k : Keypair)
      (resident : d.keypairs[id]? = some k) (live : 0 < k.refcount)
      (word : k.peer ≠ none) :
      ClearPut (some id) d (Index.releasedDevice d id k true)

/-- Every step reads the current peer and clears its slot before releasing. -/
inductive ClearRun (pid : PeerId) : Device → List ClearSlot → Device → Prop
  | nil (d : Device) : ClearRun pid d [] d
  | cons (d : Device) (slot : ClearSlot) (p : Peer) (middle final : Device)
      (rest : List ClearSlot) (resident : d.peers[pid]? = some p)
      (put : ClearPut (slot.read p) (clearWrite d pid slot p) middle)
      (tail : ClearRun pid middle rest final) :
      ClearRun pid d (slot :: rest) final

/-- A static local reference budget. Aliases count once per occurrence;
no ownership equality or distinctness is assumed. -/
def ClearReady (d : Device) (keys : List (Option KeypairId)) : Prop :=
  ∀ id, 0 < keys.count (some id) → ∃ k,
    d.keypairs[id]? = some k ∧ k.peer ≠ none ∧ keys.count (some id) ≤ k.refcount

def clearKeys (p : Peer) : List (Option KeypairId) :=
  [p.keypairNext, p.keypairPrevious, p.keypairCurrent]

end Leanux.Proofs.WG.Noise
