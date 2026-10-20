import AllowedipsSourceModel
import SourceAdapter

namespace Binary.Pair.Allowedips.Model
open Leanux

-- Copied from Leanux/Proofs/Framing/Lift.lean at eba3c2b6; no proof-tree import.
theorem liftAip_run (a : WG.AipM α) (g : WGWorld) (ambient : Ambient) :
    ((WG.liftAip a).run g).run ambient =
      match g.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d =>
          ((a.run {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}).run ambient).map
            (fun ((x, s), ambient') =>
              ((x, {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}), ambient')) := by
  cases hd : g.dev with
  | none =>
    simp [WG.liftAip, WG.getDev, hd, invariant, AmbientM.invariant]
    rfl
  | some d =>
    simp only [WG.liftAip, WG.getDev, StateT.run_bind, StateT.run_pure]
    cases ha : (a.run {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}).run ambient <;>
      simp [WG.modifyDev, hd, ha] <;> rfl


private def delBody (id : Nat) (entry : Nat × WG.Peer) (_ : PUnit) : WG.M (ForInStep PUnit) := do
  if entry.2.allowedipsList.contains id then
    WG.setPeer entry.1 (unlist id entry.2)
  pure (.yield PUnit.unit)

private theorem delBody_run (id : Nat) (entry : Nat × WG.Peer)
    (k : WGWorld) (d : WG.Device) (ambient : Ambient) :
    ((delBody id entry PUnit.unit).run {k with dev := some d}).run ambient =
      .ok ((.yield PUnit.unit,{k with dev := some {d with peers := delStep id d.peers entry}}),ambient) := by
  by_cases member : entry.2.allowedipsList.contains id
  · simp only [delBody,delStep,member,ite_true]; rfl
  · simp only [delBody,delStep,member]; rfl

private theorem listDel_loop (xs : List (Nat × WG.Peer)) (id : Nat)
    (k : WGWorld) (d : WG.Device) (ambient : Ambient) :
    ((forIn xs PUnit.unit (delBody id)).run {k with dev := some d}).run ambient =
      .ok ((PUnit.unit,{k with dev := some {d with peers := delFold id xs d.peers}}),ambient) := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons,StateT.run_bind,delBody_run,Source.except_ok_bind]
    exact ih {d with peers := delStep id d.peers x}

theorem listDel_run (k : WGWorld) (d : WG.Device) (ambient : Ambient)
    (hasDevice : k.dev=some d) (id : Nat) :
    ((WG.listDel id).run k).run ambient =
      .ok (((),{k with dev := some (unlisted d id)}),ambient) := by
  have installed : {k with dev := some d}=k := by rw [←hasDevice]
  have run := listDel_loop d.peers.toList id k d ambient
  rw [installed] at run
  have getRun : ((WG.getDev).run k).run ambient = .ok ((d,k),ambient) := by
    simp [WG.getDev,hasDevice]
  simp only [WG.listDel,StateT.run_bind,getRun,Source.except_ok_bind]
  change ((forIn d.peers.toList PUnit.unit (delBody id)).run k).run ambient >>= _ = _
  rw [run]
  rfl

theorem listAddTail_run (k : WGWorld) (d : WG.Device) (ambient : Ambient)
    (hasDevice : k.dev=some d) (pid id : Nat) (peer : WG.Peer)
    (hasPeer : d.peers[pid]?=some peer) :
    ((WG.listAddTail pid id).run k).run ambient =
      .ok (((),{k with dev := some {d with peers := d.peers.insert pid {peer with allowedipsList := peer.allowedipsList++[id]}}}),ambient) := by
  simp [WG.listAddTail,WG.getPeer,WG.getDev,WG.setPeer,WG.modifyDev,hasDevice,hasPeer]

end Binary.Pair.Allowedips.Model
