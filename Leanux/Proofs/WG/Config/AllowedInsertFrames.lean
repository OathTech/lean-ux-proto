import Leanux.Proofs.WG.Noise.CryptoFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Node-site variant of Keypairs.hiddenAlloc_sameKernel in
Leanux/Proofs/WG/Keypairs/OrdinaryHot.lean, whose import currently pulls the failing
inherited counter refinement. The proof reuses the shape of the C2
Noise.keypairAllocation_kernel_spec and keeps the original allocation loop. -/
theorem hiddenAlloc_sameKernel_node_spec_variant (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenAlloc .allocNode190 ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  noise_vcgen [hiddenAlloc, _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord,
    _private.Leanux.Kernel.Defs.«0».Leanux.allocPlaceholder, invariant, unsupported, hh]
  case inv1 _ n _ _ _ _ _ _ => exact fun r _ => ⟨n - r.2 + 1⟩
  case inv2 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry, ExceptConds.true, ExceptConds.const]
  all_goals omega

end Leanux.Proofs.WG.Config
