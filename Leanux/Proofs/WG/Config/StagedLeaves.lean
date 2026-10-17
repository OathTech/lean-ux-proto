import Leanux.Proofs.WG.Config.StagedFallback

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def clearedStaged (d : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer d pid { p with staged := [] }

theorem staged_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : p.staged = []) :
    Returns (sendStagedPackets pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some d) := by
  intro g ambient device
  refine ⟨(), g, {ambient with steps := ambient.steps.push {
    decision := .stagedEmpty, outcome := true, netRx := ambient.netRxSection}}, ?_, device⟩
  rw [← sendStaged_source]
  simp [stagedSource, getPeer, getDev, device, resident, empty, branch, AmbientM.branch]
  rfl

namespace Product

theorem staged_compose (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (nonempty : p.staged ≠ [])
    (kp : Option KeypairId) (middle : Device) (Q : Unit → World → Prop)
    (get : Noise.Product.Ensures (liftWG (keypairGet p.keypairCurrent))
      (fun w => w.wg.dev = some (clearedStaged d pid p))
      (fun result w => result = kp ∧ w.wg.dev = some middle))
    (tail : Noise.Product.Ensures (liftWG (stagedAfterGet pid p.staged kp))
      (fun w => w.wg.dev = some middle) Q) :
    Noise.Product.Ensures (liftWG (sendStagedPackets pid)) (fun w => w.wg.dev = some d) Q := by
  intro w result final device run
  let marked : World := {w with
    wg := {w.wg with dev := some (clearedStaged d pid p)}
    ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .stagedEmpty, outcome := false, netRx := w.ambient.netRxSection}}}
  have notEmpty : p.staged.isEmpty = false := by cases items : p.staged <;> simp_all
  have nativeFactor : ((stagedSource pid).run w.wg).run w.ambient =
      (((keypairGet p.keypairCurrent).run marked.wg).run marked.ambient >>= fun ((key, current), inputs) =>
        ((stagedAfterGet pid p.staged key).run current).run inputs) := by
    simp [stagedSource, getPeer, getDev, device, resident, nonempty, notEmpty,
      branch, AmbientM.branch, setPeer, modifyDev, marked, clearedStaged, withPeer]
  have factor : (liftWG (sendStagedPackets pid)).run w =
      ((liftWG (keypairGet p.keypairCurrent)).run marked >>= fun (key, current) =>
        (liftWG (stagedAfterGet pid p.staged key)).run current) := by
    rw [← sendStaged_source]
    change ((((stagedSource pid).run w.wg).run w.ambient >>= fun ((value, current), inputs) =>
      .ok (value, {w with wg := current, ambient := inputs}))) = _
    rw [nativeFactor]
    change _ = (((((keypairGet p.keypairCurrent).run marked.wg).run marked.ambient) >>=
      fun ((value, next), after) => .ok (value, {marked with wg := next, ambient := after})) >>= _)
    cases acquired : ((keypairGet p.keypairCurrent).run marked.wg).run marked.ambient with
    | error err => rfl
    | ok out =>
      obtain ⟨⟨key, current⟩, inputs⟩ := out
      rfl
  rw [factor] at run
  cases acquired : (liftWG (keypairGet p.keypairCurrent)).run marked with
  | error err => rw [acquired] at run; cases run
  | ok pair =>
    obtain ⟨key, current⟩ := pair
    rw [acquired] at run
    obtain ⟨same, state⟩ := get marked key current rfl acquired
    subst key
    exact tail current result final state run
end Product

theorem keypairGet_missing (id : KeypairId) (d : Device) (missing : d.keypairs[id]? = none) :
    Ensures (keypairGet (some id)) (fun g => g.dev = some d) (fun _ _ => False) := by
  intro g ambient result final after device run
  simp [keypairGet, getKeypair, getDev, device, missing, branch, AmbientM.branch,
    invariant, AmbientM.invariant] at run
  cases run

end Leanux.Proofs.WG.Config
