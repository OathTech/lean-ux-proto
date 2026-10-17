import Leanux.Proofs.WG.Index.Table

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

abbrev bucketHas := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas

def bucketWalk (walk collide : Decision) (index : Nat) (entries : List IndexEntry) : IndexM Bool := do
  for e in entries do
    _ ← branch walk true
    if ← branch collide (e.index == index) then return true
  _ ← branch walk false
  return false

theorem bucketHas_source (walk collide : Decision) (index : Nat) :
    bucketHas walk collide index = (do
      let entries ← indexBucket index
      bucketWalk walk collide index entries) := rfl

theorem bucketWalk_cons (walk collide : Decision) (index : Nat) (e : IndexEntry)
    (es : List IndexEntry) :
    bucketWalk walk collide index (e :: es) = (do
      _ ← branch walk true
      let equal ← branch collide (e.index == index)
      if equal then pure true else bucketWalk walk collide index es) := by
  simp [bucketWalk, List.forIn_cons, branch, AmbientM.branch, bind_assoc]
  split <;> simp

theorem bucketWalk_returns (walk collide : Decision) (index : Nat)
    (entries table : List IndexEntry) :
    Returns (bucketWalk walk collide index entries) (fun t => t = table)
      (fun result t => result = entries.any (·.index == index) ∧ t = table) := by
  induction entries with
  | nil =>
    intro t ambient ht
    let after := {ambient with steps := ambient.steps.push {
      decision := walk, outcome := false, netRx := ambient.netRxSection}}
    refine ⟨false, t, after, ?_, rfl, ht⟩
    simp [bucketWalk, branch, AmbientM.branch, after]
    rfl
  | cons e es ih =>
    intro t ambient ht
    let next := {ambient with steps := (ambient.steps.push {
      decision := walk, outcome := true, netRx := ambient.netRxSection}).push {
      decision := collide, outcome := e.index == index, netRx := ambient.netRxSection}}
    cases matched : e.index == index with
    | true =>
      refine ⟨true, t, next, ?_, ?_, ht⟩
      · rw [bucketWalk_cons]
        simp [branch, AmbientM.branch, matched, next]
        rfl
      · simp [matched]
    | false =>
      obtain ⟨result, final, after, run, found, state⟩ := ih t next ht
      refine ⟨result, final, after, ?_, ?_, state⟩
      · rw [bucketWalk_cons]
        simpa [StateT.run_bind, Except.bind, Except.map, branch, AmbientM.branch,
          matched, next] using run
      · simpa [matched] using found

theorem bucket_any (index : Nat) (table : List IndexEntry) :
    (bucket index table).any (·.index == index) = table.any (·.index == index) := by
  simp only [bucket, List.any_filter]
  congr 1
  funext e
  by_cases same : e.index = index <;> simp [same]

theorem bucketHas_returns (walk collide : Decision) (index : Nat) (d : Device) :
    Returns (liftIndex (bucketHas walk collide index)) (fun g => g.dev = some d)
      (fun result g => result = d.indexTable.any (·.index == index) ∧ g.dev = some d) := by
  intro g ambient device
  obtain ⟨result, table, after, run, found, same⟩ :=
    bucketWalk_returns walk collide index (bucket index d.indexTable)
      d.indexTable d.indexTable ambient rfl
  subst table
  refine ⟨result, {g with dev := some d}, after, ?_, ?_, rfl⟩
  · rw [bucketHas_source]
    simp [liftIndex, getDev, device, indexBucket, bucket, StateT.run_bind, modifyDev] at *
    rw [run]
    rfl
  · simpa [bucket_any] using found

end Leanux.Proofs.WG.Index
