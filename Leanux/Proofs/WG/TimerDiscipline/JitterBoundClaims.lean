import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.Campaign2.Bridge

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The original projected contract: preserve the WireGuard core and bound
any normally returned jitter value, without asserting completion. -/
theorem projected_jitter_bound (site : HiddenSite) (initial : Core) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site) (fun s => s.wg.toCore = initial)
      (fun n s => s.wg.toCore = initial ∧ n < HZ / 3) := by
  intro g ambient n final after pre run
  exact ⟨jitter_wg_spec (fun g => core g = initial) site g ambient n final after pre run,
    jitter_bounded site g ambient n final after trivial run⟩

/-- The surviving WireGuard portion of the former Kernel equality is Core.
This source companion proves the stronger full WireGuard-state preservation.
The initial observation is universally quantified; there is no device, record,
or readiness assumption. Excluded subsystem preservation follows from WG.M. -/
theorem source_jitter_bound (site : HiddenSite) (initial : Campaign2.State) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site) (fun s => s.wg = initial)
      (fun n s => s.wg = initial ∧ n < HZ / 3) := by
  intro g ambient n final after pre run
  exact ⟨jitter_wg_spec (fun g => (snapshot g ambient).wg = initial)
      site g ambient n final after pre run,
    jitter_bounded site g ambient n final after trivial run⟩

end Leanux.Proofs.WG.TimerDiscipline
