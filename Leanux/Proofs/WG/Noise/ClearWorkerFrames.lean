import Leanux.Proofs.WG.Noise.SessionTagSource
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ClearWorker
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- Pure consequence of the existing ordered clear relation. -/
theorem clearRun_tagMap {pid : PeerId} {d final : Device} {slots : List ClearSlot}
    (steps : ClearRun pid d slots final) :
    responseTagMap (some final) = responseTagMap (some d) := by
  induction steps with
  | nil => rfl
  | cons d slot p middle final rest resident put tail ih =>
    refine ih.trans ?_
    change responseTagMap (some middle) = _
    have unchanged : responseTagMap (some middle) =
        responseTagMap (some (clearWrite d pid slot p)) := by
      funext target
      simp only [responseTagMap, Option.bind_some, clearPut_peers put]
    rw [unchanged]
    exact tagMap_write d pid p (slot.clear p) resident (by cases slot <;> rfl)

/-- Local peerPut frame variant of Keypairs.WGFrames.peerPut_spec.
The complete optional tag map includes actual last-reference deletion.
The positive reference count is derived from the normal original run. -/
theorem peerPut_spec_clearTagMap_variant (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (peerPut (some pid)) (fun g => g.dev = some d)
      (fun _ g => 0 < p.refcount ∧ ∀ target, responseTagMap g.dev target =
        if pid = target then
          if p.refcount = 1 then none else some p.handshakeState
        else responseTagMap (some d) target) := by
  intro g ambient result final after device run
  by_cases positive : 0 < p.refcount
  · refine ⟨positive, ?_⟩
    by_cases last : p.refcount = 1
    · have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
      cases result
      simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
        refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
        hl, liftIndex, retirePeerUnits, modifyAmbient,
        device, resident, last, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
        invariant, AmbientM.invariant] at run
      repeat' first | split at run | contradiction
      all_goals rcases run with ⟨rfl, rfl⟩
      all_goals
        intro target
        by_cases same : pid = target
        · subst target
          simp [responseTagMap,last]
        · simp [responseTagMap,Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert,same]
    · have held : 1 < p.refcount := by omega
      have effect := (ensures_iff _ _ _).mpr
        (Config.peerPut_retained pid d p resident held) g ambient result final after device run
      rw [effect]
      intro target
      by_cases same : pid = target
      · subst target
        simp [Config.withPeer,responseTagMap,last]
      · simp [Config.withPeer,responseTagMap,Std.TreeMap.getElem?_insert,same]
  · have zero : p.refcount = 0 := by omega
    simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
      refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
      device, resident, zero, unsupported, AmbientM.unsupported] at run
    cases run


end Leanux.Proofs.WG.Noise.ClearWorker
