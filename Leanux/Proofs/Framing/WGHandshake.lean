import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.KernelEffects
import Leanux.WG.Handshake

/-! Canonical full-kernel frames for the original access-free Noise helpers.
Their branches and record failures are unchanged. These frames alone do not
establish call coverage; callers inspect and observe every store access. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem generatePublic_sameKernel (secret : Key) : SameKernel (generatePublic secret) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [generatePublic, branch]

theorem kdf_sameKernel (second third : Bool) (chainingKey data : List UInt8) :
    SameKernel (kdf second third chainingKey data) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [kdf, WG.orM, branch]

theorem kdfOut_sameKernel (outs : List (List UInt8)) (i : Nat) : SameKernel (kdfOut outs i) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [kdfOut, invariant]

theorem messageEphemeral_sameKernel (copy : Bool) (e ck hash : List UInt8) :
    SameKernel (messageEphemeral copy e ck hash) := by
  apply sameKernel_of_wp
  intro k
  have hk := fun second third ck data => sameKernel_wp _ (kdf_sameKernel second third ck data) (fun s => s = k)
  have ho := fun outs i => sameKernel_wp _ (kdfOut_sameKernel outs i) (fun s => s = k)
  mvcgen [messageEphemeral, hk, ho, branch]

theorem mixDh_sameKernel (key : Bool) (ck priv pub : List UInt8) :
    SameKernel (mixDh key ck priv pub) := by
  apply sameKernel_of_wp
  intro k
  have hk := fun second third ck data => sameKernel_wp _ (kdf_sameKernel second third ck data) (fun s => s = k)
  have ho := fun outs i => sameKernel_wp _ (kdfOut_sameKernel outs i) (fun s => s = k)
  mvcgen [mixDh, hk, ho, branch]

theorem mixPrecomputedDh_sameKernel (ck precomputed : List UInt8) :
    SameKernel (mixPrecomputedDh ck precomputed) := by
  apply sameKernel_of_wp
  intro k
  have hk := fun second third ck data => sameKernel_wp _ (kdf_sameKernel second third ck data) (fun s => s = k)
  have ho := fun outs i => sameKernel_wp _ (kdfOut_sameKernel outs i) (fun s => s = k)
  mvcgen [mixPrecomputedDh, hk, ho, branch]

theorem messageDecrypt_sameKernel (sealed key hash : List UInt8) :
    SameKernel (messageDecrypt sealed key hash) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [messageDecrypt, branch, invariant]

end Leanux.Proofs.Framing
