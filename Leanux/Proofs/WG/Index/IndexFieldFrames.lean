import Leanux.Proofs.WG.Noise.StateEdges
import Leanux.Proofs.WG.Index.Allocation
import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Device residency and numeric uniqueness of its index table. -/
def IndicesSafe (w : World) : Prop :=
  ∃ d, w.k.wg = some d ∧ UniqueIndices d.indexTable

theorem setPeer_indices_spec (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [IndicesSafe]
  all_goals grind

theorem setKeypair_indices_spec (id : KeypairId) (kp : Keypair) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setKeypair id kp ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  mvcgen [setKeypair, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [IndicesSafe]
  all_goals grind

theorem handshakeZero_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  have hs := setPeer_indices_spec
  mvcgen [handshakeZero, getPeer, getDev, getK, invariant, hs]

theorem deriveKeys_indices_spec (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueIndices d.indexTable
  have hh := hiddenClock64_kernel_spec P
  have hk := kdf_wg_spec P
  have ho := kdfOut_wg_spec P
  have hs := setKeypair_indices_spec
  mvcgen [deriveKeys, getKeypair, getDev, getK, invariant, hh, hk, ho, hs]

theorem keypairCreate_indices_spec (peer : Option PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ keypairCreate peer ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique⟩ := pre
  have effect := keypairCreate_exact peer d w.k.keypairCounter w result final ⟨device, rfl⟩ run
  cases result with
  | none => exact ⟨d, effect.1, unique⟩
  | some id => exact ⟨_, effect.2.1, unique⟩

end Leanux.Proofs.WG.Index
