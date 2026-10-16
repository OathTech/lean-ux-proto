import Leanux.Proofs.WG.Noise.StateEdges

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- A prefix may be forgotten only when the suffix establishes its own
postcondition. This lemma deliberately promises no state preservation. -/
theorem unconstrained_prefix (a : M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  rw [← ensures_iff]
  intro _ _ _ _ _
  trivial

theorem consumeInitiation_tag (msg : List UInt8) :
    Ensures (consumeInitiation msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w.k pid = some HANDSHAKE_CONSUMED_INITIATION) := by
  rw [ensures_iff]
  have hp := fun key => unconstrained_prefix (pubkeyLookup key)
  have hf := fun pid => unconstrained_prefix (peerPut pid)
  have hh := hiddenClock64_kernel_spec (fun _ => True)
  have he := messageEphemeral_wg_spec (fun _ => True)
  have hd := mixDh_wg_spec (fun _ => True)
  have hs := mixPrecomputedDh_wg_spec (fun _ => True)
  have hm := messageDecrypt_wg_spec (fun _ => True)
  mvcgen -trivial [consumeInitiation, Leanux.WG.orM, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, hp, hf, hh, he, hd, hs, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [tagAt, peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals try trivial
  all_goals try simp_all [ExceptConds.true, ExceptConds.const]
  all_goals grind only

theorem consumeResponse_tag (msg : List UInt8) :
    Ensures (consumeResponse msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w.k pid = some HANDSHAKE_CONSUMED_RESPONSE) := by
  rw [ensures_iff]
  have hi := fun kinds index => unconstrained_prefix (indexLookup kinds index)
  have hf := fun pid => unconstrained_prefix (peerPut pid)
  have he := messageEphemeral_wg_spec (fun _ => True)
  have hd := mixDh_wg_spec (fun _ => True)
  have hk := kdf_wg_spec (fun _ => True)
  have ho := kdfOut_wg_spec (fun _ => True)
  have hm := messageDecrypt_wg_spec (fun _ => True)
  mvcgen [consumeResponse, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, hi, hf, he, hd, hk, ho, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [tagAt, peerAt, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals grind

end Leanux.Proofs.WG.Noise
