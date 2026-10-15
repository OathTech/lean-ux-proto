import TrieHeap
import LookupProjection
import PeerCountPhase

namespace Binary.AllowedipsRelation
open Leanux Leanux.WG

/-- The final peer-bearing trie node and its peer identity, fixed from the
    incoming source search. Intermediate candidates do not add count reads. -/
structure Focus where
  node : Option NodeId
  peer : Option PeerId

structure Config where
  root : Option NodeId
  bits : Nat
  key : Nat
  nodes : NodeId → Address
  peers : PeerId → Address
  focus : Focus
  incomingSteps : List Step
  rxSection : Nat

/-- Only the trie search and the selected helper count are represented.
    The function-valued view does not assert equality outside reached nodes:
    TrieHeap determines exactly which fields and bytes are related. -/
structure View where
  nodes : NodeId → Option AipNode
  count : Option Nat

def project (c : Config) (w : World) : Option View := do
  let d ← w.k.wg
  return ⟨fun id => d.nodes.get? id,
    c.focus.peer.bind (fun id => (d.peers.get? id).map (·.refcount))⟩

def Physical (c : Config) (raw : List MachineState)
    (seen : List LookupObservation.Point) (s : MachineState) (v : View) : Prop :=
  TrieHeap s.data.dmem c.nodes c.peers v.nodes c.root c.bits c.key ∧
  match c.focus.peer with
  | none => v.count = none
  | some pid => ∃ count,
      v.count = some count ∧ c.peers pid ≠ 0 ∧
      PeerCountPhase.At (LookupRelation.countPhase raw seen) s.data.dmem
        (c.peers pid + .ofNat 64 Layouts.peer_refcount) count

def StepsAt (c : Config) (seen : List LookupObservation.Point) (w : World) : Prop :=
  w.steps.toList = c.incomingSteps ++ seen.filterMap (·.step) ∧
  w.netRxSection = c.rxSection

/-- Minimal WireGuard projection. Raw execution and observed decisions are
    parameters bound to actual prefixes by the eventual correspondence
    theorem; they are not physical or supplied-environment World fields. -/
def R (c : Config) (raw : List MachineState)
    (seen : List LookupObservation.Point) (s : MachineState) (w : World) : Prop :=
  raw.getLast? = some s ∧
  (∃ v, project c w = some v ∧ Physical c raw seen s v) ∧ StepsAt c seen w

def Reads (c : Config) (v : View) (a : Address) : Prop :=
  TrieReads c.nodes v.nodes c.root c.bits c.key a ∨
  ∃ pid, c.focus.peer = some pid ∧
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

theorem Physical.frame (c : Config) (raw nextRaw : List MachineState)
    (seen nextSeen : List LookupObservation.Point) (s t : MachineState) (v : View)
    (physical : Physical c raw seen s v)
    (phase : LookupRelation.countPhase nextRaw nextSeen = LookupRelation.countPhase raw seen)
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ a, Reads c v a → ¬writes a) :
    Physical c nextRaw nextSeen t v := by
  refine ⟨physical.1.frame frame (fun a h => apart a (.inl h)), ?_⟩
  cases focus : c.focus.peer with
  | none => simpa only [Physical, focus] using physical.2
  | some pid =>
    obtain ⟨count, eq, nonnull, loaded⟩ := physical.2 |> (by simpa only [focus] using ·)
    refine ⟨count, eq, nonnull, ?_⟩
    rw [phase]
    exact PeerCountPhase.At.frame frame
      (fun i hi => apart _ (.inr ⟨pid, focus, i, hi, rfl⟩)) loaded

#print axioms Physical.frame
end Binary.AllowedipsRelation
