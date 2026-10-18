import Leanux.Proofs.WG.HandshakeSecurity.FreshnessFrames
import Leanux.Proofs.WG.HandshakeSecurity.Increasing

/-! Retained-peer timestamp history. The replay store includes allocation
identity. Deletion is allowed by coherence; inserting a new peer requires a
separate allocation event before this history can cover that operation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

def TimestampReceipt.apply (r : TimestampReceipt)
    (store : PeerId → Option (Nat × List UInt8)) : PeerId → Option (Nat × List UInt8) :=
  fun pid => if pid = r.peer then
    (freshnessAt r.execution.before r.peer).map fun stamp => (stamp.1, r.received)
  else store pid

def replayTimestamps (initial : WGWorld) (h : List TimestampReceipt) :
    PeerId → Option (Nat × List UInt8) :=
  h.foldl (fun store r => r.apply store) (freshnessAt initial)

theorem replayTimestamps_append_one (initial : WGWorld) (h : List TimestampReceipt)
    (r : TimestampReceipt) :
    replayTimestamps initial (h ++ [r]) = r.apply (replayTimestamps initial h) := by
  simp [replayTimestamps, List.foldl_append]

inductive TimestampHistory (initial : WGWorld) : List TimestampReceipt → Prop where
  | empty : TimestampHistory initial []
  | next {h : List TimestampReceipt} (r : TimestampReceipt)
      (prior : TimestampHistory initial h) (valid : r.Valid)
      (linked : ∃ identity old,
        replayTimestamps initial h r.peer = some (identity, old) ∧
        freshnessAt r.execution.before r.peer = some (identity, old) ∧
        memcmp r.received old = .gt) : TimestampHistory initial (h ++ [r])

def TimestampCoherent (initial : WGWorld) (h : List TimestampReceipt) (w : WGWorld) : Prop :=
  ∀ pid stamp, freshnessAt w pid = some stamp → replayTimestamps initial h pid = some stamp

def TimestampInv (initial : WGWorld) (h : List TimestampReceipt) (w : WGWorld) : Prop :=
  TimestampHistory initial h ∧ TimestampCoherent initial h w

theorem TimestampInv.initial (initial : WGWorld) : TimestampInv initial [] initial :=
  ⟨.empty, fun _ _ h => h⟩

theorem TimestampCoherent.retained {initial w v : WGWorld} {h : List TimestampReceipt}
    (coherent : TimestampCoherent initial h w) (frame : RetainsFreshness w v) :
    TimestampCoherent initial h v := fun pid stamp found => coherent pid stamp (frame pid stamp found)

theorem history_append (initial : WGWorld) (h : List TimestampReceipt) (r : TimestampReceipt)
    (hi : TimestampInv initial h r.execution.before) (valid : r.Valid)
    (newer : r.Increasing) : TimestampInv initial (h ++ [r]) r.execution.after := by
  obtain ⟨d, p, hd, hp, after, _⟩ := write_effect r.peer r.received r.execution valid
  have before : freshnessAt r.execution.before r.peer = some (p.internalId, p.latestTimestamp) := by
    simp [freshnessAt, hd, hp]
  have increase : memcmp r.received p.latestTimestamp = .gt := by
    obtain ⟨old, actual, comparison⟩ := newer
    have equal : p.latestTimestamp = old := by simpa [latestAt, hd, hp] using actual
    simpa [equal] using comparison
  refine ⟨.next r hi.1 valid ⟨p.internalId, p.latestTimestamp,
    hi.2 r.peer _ before, before, increase⟩, ?_⟩
  intro pid stamp found
  rw [replayTimestamps_append_one]
  unfold TimestampReceipt.apply
  by_cases same : pid = r.peer
  · subst pid
    simp only [ite_true, before, Option.map_some]
    simpa [freshnessAt, after] using found
  · have old : freshnessAt r.execution.before pid = some stamp := by
      simpa [freshnessAt, after, hd, Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq, Ne.symm same] using found
    simpa [same] using hi.2 pid stamp old

end Leanux.Proofs.WG.HandshakeSecurity
