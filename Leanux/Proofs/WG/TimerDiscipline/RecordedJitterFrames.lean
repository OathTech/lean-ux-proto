import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Recorded-mode variant of jitter_bounded, also framing the mode bit. -/
theorem jitter_recorded_bounded (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k ∧ w.armRecords = true⌝⦄ jitterBelowRekeyTimeout site
      ⦃⇓? n w => ⌜(P w.k ∧ w.armRecords = true) ∧ n < HZ / 3⌝⦄ := by
  have byte_bound (bs : List UInt8) : 83 * (bs[0]?.getD default).toNat / 256 < 83 := by
    have hb := UInt8.toNat_lt_size (bs[0]?.getD default)
    change _ < 256 at hb
    omega
  have hh := hidden_recorded_kernel_spec P
  mvcgen [jitterBelowRekeyTimeout, recordBudget, budgetExhausted, invariant, unsupported, hh]
  case inv1 => exact (⇓? r w => ⌜(P w.k ∧ w.armRecords = true) ∧
    ∀ n, r.2.1 = some n → n < HZ / 3⌝)
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [HZ, ExceptConds.true, ExceptConds.const]
  all_goals try omega
  all_goals exact byte_bound _


end Leanux.Proofs.WG.TimerDiscipline
