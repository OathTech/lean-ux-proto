import Leanux.Proofs.WG.Noise.ConfirmationReinstallModel
import Leanux.Proofs.WG.Noise.RotationClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

namespace ConfirmationReinstallWitness

/-- Direct reuse of the installation helper, not beginSession or allocation. -/
def calls : WG.M (Bool × Bool) := do
  let first ← receivedWithKeypair 0 0
  addNewKeypair 0 0
  let second ← receivedWithKeypair 0 0
  return (first, second)

end ConfirmationReinstallWitness
open ConfirmationReinstallWitness

/-- Every Ambient realizes both confirmations. The direct reinstallation leaves
this resident key unchanged and does not allocate a new serial or cursor. -/
theorem confirmationReinstallWitness_returns (counter : Nat) :
    Campaign2.Returns calls
      (fun s => s.wg.device = some device ∧ s.wg.keypairCounter = counter)
      (fun result after => result = (true, true) ∧
        after.wg.keypairCounter = counter ∧ ∃ final,
        after.wg.device = some final ∧ final.keypairs[0]? = some key ∧
        final.nextKeypairId = device.nextKeypairId ∧ ∃ p,
        final.peers[0]? = some p ∧ p.keypairPrevious = some 0 ∧
        p.keypairCurrent = some 0 ∧ p.keypairNext = none) := by
  intro g ambient pre
  have hd : g.dev = some device := pre.1
  have hc : g.keypairCounter = counter := pre.2
  have writeForm (pid : PeerId) (f : Peer → Peer) :
      modifyPeer pid f = (do let q ← getPeer pid; setPeer pid (f q)) := rfl
  simp only [calls, receivedWithKeypair_rotation_source, addNewKeypair_rotation_source]
  simp [confirmationSource, rotationSource, rotationExecute, confirmationPlan,
    rotateResponder, RotationWrite.apply, getPeer, getKeypair, getDev, hd,
    writeForm, setPeer, modifyDev, keypairPut, branch, AmbientM.branch,
    device, peer, key,
    Campaign2.snapshot, Campaign2.core, hc]
  refine ⟨_, ⟨_, rfl⟩, rfl, _, rfl, ?_, rfl,
    {peer with keypairPrevious := some 0, keypairCurrent := some 0, keypairNext := none},
    ?_, rfl, rfl, rfl⟩ <;> simp [peer]


end Leanux.Proofs.WG.Noise
