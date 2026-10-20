import SourceAdapter
import AllowedipsSourceSelect

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory

/-- Nonempty loop body after the actual findNodeNode=true decision. -/
def nodeBody (bits key id : Nat) (previous : Option NodeId) : Logged (ForInStep Acc) := do
  let mut found := previous
  let n ← StateT.lift (Source.getNode id)
  let matching ← prefixMatches n key bits
  if !(← branchLogged .findNodePrefixMatches matching) then
    return .done (some found, some id, found)
  if ← branchLogged .findNodeHasPeer n.peer.isSome then found := some id
  if ← branchLogged .findNodeFullLength (n.cidr == bits) then
    return .done (some found, some id, found)
  let bit ← StateT.lift (choose n key)
  let next ← StateT.lift (n.bitAt bit)
  return .yield (none,next,found)

theorem iteration_some (bits key id : Nat) (answer : Option (Option NodeId))
    (found : Option NodeId) :
    iteration bits key (answer,some id,found) = (do
      _ ← branchLogged .findNodeNode true
      nodeBody bits key id found) := rfl

/-- Remaining search after the nonempty guard. `fuel` counts subsequent
iterations; exhaustion still runs the mirror's explicit failure in finish. -/
def afterGuard (bits key fuel id : Nat) (found : Option NodeId) : Logged (Option NodeId) := do
  match ← nodeBody bits key id found with
  | .done result => finish result
  | .yield next => do
    let result ← loop bits key fuel next
    finish result

theorem loop_some_finish (bits key fuel id : Nat) (answer : Option (Option NodeId))
    (found : Option NodeId) :
    (do let result ← loop bits key (fuel+1) (answer,some id,found); finish result) =
    (do _ ← branchLogged .findNodeNode true; afterGuard bits key fuel id found) := by
  simp only [loop,iteration_some,bind_assoc,afterGuard]
  congr 1
  funext _
  congr 1
  funext step
  cases step <;> simp only [pure_bind]

theorem findNode_some (bits key id : Nat) :
    findNode (some id) bits key =
      (do _ ← branchLogged .findNodeNode true; afterGuard bits key 129 id none) := by
  rw [findNode_bounded]
  exact loop_some_finish bits key 129 id none none

/-- This is the source boundary used at physical lookup+d5: the node=true
point has already been emitted, but common_bits has not yet been called. -/
theorem findNode_some_afterGuard (bits key id : Nat) (history points : List Point)
    (w final : World) (answer : Option NodeId)
    (accepted : ((findNode (some id) bits key).run history).run w =
      .ok ((answer,points),final)) :
    ((afterGuard bits key 129 id none).run
      (history ++ [⟨.decision .findNodeNode,LookupMirror.record w .findNodeNode true⟩])).run
        (LookupMirror.record w .findNodeNode true) = .ok ((answer,points),final) := by
  rw [findNode_some] at accepted
  exact accepted

#print axioms iteration_some
#print axioms loop_some_finish
#print axioms findNode_some_afterGuard
end Binary.AllowedipsSource
