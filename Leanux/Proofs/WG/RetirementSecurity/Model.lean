import Leanux.Proofs.WG.Lifetimes.KeypairRelease

/-! The key store and index projection used by local retirement contracts.
Reference accounting here concerns keypairs, not the separate peer ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

def keyAt (w : WGWorld) (id : KeypairId) : Option Keypair :=
  w.dev.bind fun d => d.keypairs[id]?

def indexAt (w : WGWorld) : Option (List IndexEntry) :=
  w.dev.map (·.indexTable)

def peersAt (w : WGWorld) := w.dev.map (·.peers)

def withoutKeyIndex (id : KeypairId) (entries : List IndexEntry) : List IndexEntry :=
  entries.filter fun e => !(e.owner == .keypair id)

def keyAfterPut (k : Keypair) : Option Keypair :=
  if k.refcount = 1 then none else some {k with refcount := k.refcount - 1}

def references (w : WGWorld) (id : KeypairId) : Nat :=
  ((keyAt w id).map (·.refcount)).getD 0

def Unpublished (id : KeypairId) (w : WGWorld) : Prop :=
  ∀ entries, indexAt w = some entries → ∀ entry ∈ entries, entry.owner ≠ .keypair id

/-- One successful original put pays one key reference. Unpublication and
allocation removal remain separate: either may occur without the other. -/
structure PutEffect (id : KeypairId) (now : Bool) (k : Keypair)
    (before after : WGWorld) : Prop where
  positive : 0 < k.refcount
  frontier : after.keypairCounter = before.keypairCounter
  peers : peersAt after = peersAt before
  selected : keyAt after id = keyAfterPut k
  others : ∀ other, other ≠ id → keyAt after other = keyAt before other
  index : indexAt after = (indexAt before).map fun entries =>
    if now || k.refcount == 1 then withoutKeyIndex id entries else entries

end Leanux.Proofs.WG.RetirementSecurity
