import Leanux.Proofs.WG.Index.AllocationModel
import Leanux.Proofs.WG.Index.PeerWords
import Leanux.Proofs.WG.Noise.KernelFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem keypairCreate_exact (peer : Option PeerId) (d : Device) (counter : Nat) :
    Ensures (keypairCreate peer) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun result w => match result with
        | none => w.k.wg = some d ∧ w.k.keypairCounter = counter
        | some id => id = d.nextKeypairId ∧
          w.k.wg = some (createdDevice d counter peer) ∧ w.k.keypairCounter = counter + 1) := by
  have hh := keypairAllocation_kernel_spec
    (fun k => k.wg = some d ∧ k.keypairCounter = counter)
  rw [ensures_iff]
  mvcgen [keypairCreate, getDev, getK, setKeypair, modifyDev, modifyK, branch, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [createdDevice]

end Leanux.Proofs.WG.Index
