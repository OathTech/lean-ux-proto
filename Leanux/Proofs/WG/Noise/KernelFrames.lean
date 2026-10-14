import Leanux.Proofs.WG.Noise.Basic

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem hidden_kernel_spec (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k⌝⦄ hidden site ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [hidden, skipAmbient, noteNetRxStart]

theorem hiddenClock64_kernel_spec (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenClock64 site ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hs := hidden_kernel_spec P
  mvcgen [hiddenClock64, hiddenClock, hs]

theorem kdf_kernel_spec (P : Kernel → Prop) (second third : Bool) (ck data : List UInt8) :
    ⦃fun w => ⌜P w.k⌝⦄ kdf second third ck data ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [kdf, Leanux.WG.orM, branch]

theorem kdfOut_kernel_spec (P : Kernel → Prop) (outs : List (List UInt8)) (i : Nat) :
    ⦃fun w => ⌜P w.k⌝⦄ kdfOut outs i ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [kdfOut, invariant]

theorem messageEphemeral_kernel_spec (P : Kernel → Prop) (copy : Bool)
    (e ck hash : List UInt8) :
    ⦃fun w => ⌜P w.k⌝⦄ messageEphemeral copy e ck hash ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  mvcgen [messageEphemeral, branch, hk, ho]

theorem mixDh_kernel_spec (P : Kernel → Prop) (key : Bool)
    (ck priv pub : List UInt8) :
    ⦃fun w => ⌜P w.k⌝⦄ mixDh key ck priv pub ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  mvcgen [mixDh, branch, hk, ho]

theorem mixPrecomputedDh_kernel_spec (P : Kernel → Prop) (ck precomputed : List UInt8) :
    ⦃fun w => ⌜P w.k⌝⦄ mixPrecomputedDh ck precomputed ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  mvcgen [mixPrecomputedDh, branch, hk, ho]

theorem messageDecrypt_kernel_spec (P : Kernel → Prop) (sealed key hash : List UInt8) :
    ⦃fun w => ⌜P w.k⌝⦄ messageDecrypt sealed key hash ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [messageDecrypt, branch, invariant]

theorem generatePublic_kernel_spec (P : Kernel → Prop) (secret : Key) :
    ⦃fun w => ⌜P w.k⌝⦄ generatePublic secret ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  mvcgen [generatePublic, branch]

theorem keypairAllocation_kernel_spec (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenAlloc .kzallocKeypair
    ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  noise_vcgen [hiddenAlloc, _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord,
    _private.Leanux.Kernel.Defs.«0».Leanux.allocPlaceholder, invariant, unsupported, hh]
  case inv1 _ n _ _ _ _ _ _ => exact fun r _ => ⟨n - r.2 + 1⟩
  case inv2 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry, ExceptConds.true, ExceptConds.const]
  all_goals omega

end Leanux.Proofs.WG.Noise
