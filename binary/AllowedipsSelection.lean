import Leanux.WG.AllowedIps

namespace Binary.AllowedipsSource
open Leanux Leanux.WG

def commonValue (node : AipNode) (key bits : Nat) : Nat :=
  if bits == 32 then 32 - fls (node.bits ^^^ key)
  else if bits == 128 then
    let x := node.bits ^^^ key
    let high := x / 2^64
    128 - (if high != 0 then fls high + 64 else fls (x % 2^64))
  else 0


abbrev Acc := Option (Option NodeId) × Option NodeId × Option NodeId

abbrev NodeView := NodeId → Option AipNode


/-- One source iteration without its diagnostic log. Missing nodes,
    invalid choose and missing child slots are refusal, never a miss. -/
def selectStep (nodes : NodeView) (bits key : Nat) (acc : Acc) : Option (ForInStep Acc) := do
  let current := acc.2.1
  let found := acc.2.2
  match current with
  | none => return .done (some found,current,found)
  | some id =>
    let n ← nodes id
    if commonValue n key bits < n.cidr then return .done (some found,current,found)
    let found := if n.peer.isSome then some id else found
    if n.cidr == bits then return .done (some found,current,found)
    if n.cidr ≥ n.bitlen then none
    else
      let next ← n.bit[key / 2^(n.bitlen-1-n.cidr) % 2]?
      return .yield (none,next,found)

def selectLoop (nodes : NodeView) (bits key : Nat) : Nat → Acc → Option Acc
  | 0, acc => some acc
  | fuel+1, acc => do
    match ← selectStep nodes bits key acc with
    | .done answer => return answer
    | .yield next => selectLoop nodes bits key fuel next

/-- The outer `none` means refusal (including exhausted fuel). `some none`
    is a successful trie miss. This is source selection, not a certificate
    checker or a substitute for the binary execution theorem. -/
def select (nodes : NodeView) (trie : Option NodeId) (bits key : Nat)
    (fuel : Nat := 130) : Option (Option NodeId) :=
  (selectLoop nodes bits key fuel (none,trie,none)).bind Prod.fst


end Binary.AllowedipsSource
