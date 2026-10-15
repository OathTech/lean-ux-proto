import LookupPeerSource
import BucketWorlds
import ObservationLocations

namespace Binary.LookupRelation
open Leanux Leanux.WG LookupObservation

/-- Helper decisions in source order; the machine states are the actual
    emitting successors furnished by its instruction-history theorem. -/
def peerDecisions (rx old : Nat)
    (nullPoint zeroPoint retry negative wrap dead : MachineState) : List Point :=
  [decision rx .peerGetMaybeZeroNull false nullPoint,
   decision rx .refcountAddNzZero (old == 0) zeroPoint (some (old, 0))] ++
  (if old = 0 then [] else [decision rx .refcountAddNzRetry false retry]) ++
  [decision rx .refcountAddNzNegative false negative,
   decision rx .refcountAddNzWraps false wrap,
   decision rx .peerGetMaybeZeroDead (old == 0) dead]

theorem peerDecisions_tags (rx old : Nat)
    (nullPoint zeroPoint retry negative wrap dead : MachineState) :
    LookupHistory.DecisionPoints (peerDecisions rx old nullPoint zeroPoint retry negative wrap dead) := by
  intro point member
  by_cases zero : old = 0 <;>
    simp only [peerDecisions, zero, ite_true, ite_false, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, rfl⟩

/-- Exact logged source worlds, not worlds chosen to satisfy R. -/
theorem peer_decision_worlds (world : World) (peer : Peer)
    (nullPoint zeroPoint retry negative wrap dead : MachineState) :
    LookupSearch.decisionWorlds world
      ((peerDecisions world.netRxSection peer.refcount nullPoint zeroPoint retry negative wrap dead).filterMap (·.step)) =
        MirrorHistory.peerPoints world peer := by
  by_cases zero : peer.refcount = 0 <;>
    simp [peerDecisions, MirrorHistory.peerPoints, MirrorHistory.countPoints,
      PeerMirror.countRecords, PeerMirror.recordCmp, LookupMirror.record,
      LookupSearch.decisionWorlds, LookupSearch.recordStep, decision, zero]

/-- Source commit changes no decision record or trace section. -/
theorem peer_final_log (world : World) (peer : Peer) (pid : PeerId)
    (nullPoint zeroPoint retry negative wrap dead : MachineState) :
    (PeerMirror.peerFinal pid world peer).steps =
      (LookupSearch.advance world
        ((peerDecisions world.netRxSection peer.refcount nullPoint zeroPoint retry negative wrap dead).filterMap (·.step))).steps ∧
    (PeerMirror.peerFinal pid world peer).netRxSection = world.netRxSection := by
  by_cases zero : peer.refcount = 0 <;>
    simp [peerDecisions, PeerMirror.peerFinal, PeerMirror.countRecords,
      PeerMirror.recordCmp, LookupMirror.record, LookupSearch.advance,
      LookupSearch.recordStep, decision, zero]

theorem peerDecisions_helper_tags (rx old : Nat)
    (nullPoint zeroPoint retry negative wrap dead : MachineState) :
    ∀ point ∈ peerDecisions rx old nullPoint zeroPoint retry negative wrap dead,
      HelperTag point.tag := by
  intro point member
  by_cases zero : old = 0 <;>
    simp only [peerDecisions, zero, ite_true, ite_false, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [decision, HelperTag]

#print axioms peerDecisions_helper_tags
#print axioms peerDecisions_tags
#print axioms peer_decision_worlds
#print axioms peer_final_log
end Binary.LookupRelation
