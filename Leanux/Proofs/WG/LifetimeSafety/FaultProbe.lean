import Leanux.Proofs.WG.Lifetimes.AllocationInvariant
import Leanux.Runner

/-! Bounded scope probe: the proposed initialized fault-exclusion goal and a
countermodel to deriving it from R2's allocation invariant alone. The countermodel
is an arbitrary local state, not a reachable fixture execution or a mirror bug.
-/
namespace Leanux.Proofs.WG.LifetimeSafety.FaultProbe
open Leanux Leanux.WG Leanux.Proofs.WG Leanux.Proofs.WG.Lifetimes

/-- Admission is syntactic and fixture-based; it never executes the mirror or
tests its domain verdict. Operations and hidden records remain unrestricted. -/
def ParsedDefaultWireGuard (trace : Runner.Trace) : Prop :=
  (∃ input, Runner.parseTrace input = .ok trace) ∧ trace.net = true ∧
  trace.bare = false ∧ trace.foreign = false ∧ trace.stepped = false ∧
  trace.seccompChild = false

def LookupFault : Stop → Prop
  | .invariant why => why = "no WireGuard device in this trace's fixture" ∨
      why.startsWith "dangling peer " = true ∨ why.startsWith "dangling keypair " = true
  | _ => False

/-- OPEN GOAL, not a theorem: no committed Runner stop is a peer/keypair lookup
fault for parser-admitted default network fixtures. This does not quantify over
discarded speculative trials or assert progress, successful return or reclamation. -/
def InitializedFaultExclusion : Prop :=
  ∀ trace, ParsedDefaultWireGuard trace → ∀ placeholders index failure,
    Runner.executeTrace trace placeholders = .error (index, failure) → ¬ LookupFault failure

def stalePeer : Peer :=
  { remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
    internalId := 1, keypairNext := some 7 }

def staleWorld : WGWorld :=
  { peerCounter := 1, netIfindexNext := 4,
    dev := some {
      ifindex := 3, ifname := "wg0", nextPeer := 1,
      peers := (∅ : Std.TreeMap PeerId Peer).insert 0 stalePeer,
      peerHashtable := [([], 7)] } }

def probeAmbient : Ambient := { env := Runner.harnessEnv, timing := Env.timing }

private theorem stale_allocation : AllocationInv [] staleWorld := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩)
    | (refine ⟨?_, ?_, ?_⟩)
    | skip
  all_goals simp [staleWorld, stalePeer, Peers.AccessInv, Peers.snapshot,
    AccessEvent.Safe, AccessEvent.Released, ResidentSafe, ResidentUnique, Unique,
    Absent, Bounded, identityView, keyStore, keypairResidents, packetResidents,
    Packets.deviceStore, Std.TreeMap.getElem?_insert]
  all_goals intro i; cases i <;> simp

/-- R2's allocation invariant admits dangling stored references: a public-key
lookup can fail on a missing peer, and clearing a resident peer's key slots can
fail on a missing keypair. This refutes only a local invariant-to-fault-exclusion
bridge, not the initialized goal. Lookup-history safety remains a separate claim. -/
theorem allocation_invariant_does_not_exclude_lookup_faults :
    AllocationInv [] staleWorld ∧
    ((pubkeyLookup []).run staleWorld).run probeAmbient =
      .error (.invariant "dangling peer 7") ∧
    ((keypairsClear 0).run staleWorld).run probeAmbient =
      .error (.invariant "dangling keypair 7") := by
  exact ⟨stale_allocation, rfl, rfl⟩

end Leanux.Proofs.WG.LifetimeSafety.FaultProbe
