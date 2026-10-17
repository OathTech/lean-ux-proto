import Leanux.Proofs.WG.TimerDiscipline.JitterOutcomeSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Exact product observation retains the fixture fields as well as the
native WireGuard and ambient observations. -/
theorem projected_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some (jitterStream site rejected accepted rest))
      (fun initial out => out = .ok (jitterValue accepted,
        {initial with ambient := {initial.ambient with hidden := some rest}})) := by
  intro w records
  change Campaign2.Product.observeResult
    (((jitterBelowRekeyTimeout site.hiddenSite).run w.wg).run w.ambient >>= fun ((value, g), ambient) =>
      Except.ok (value, {w with wg := g, ambient})) = _
  rw [source_jitter_records site rejected accepted rest bad good w.wg w.ambient records]
  rfl

theorem projected_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some (rejected.map (jitterRecord site)))
      (fun _ out => out = .error (.hidden s!"no record left for {site.hiddenSite.info.label}")) := by
  intro w records
  change Campaign2.Product.observeResult
    (((jitterBelowRekeyTimeout site.hiddenSite).run w.wg).run w.ambient >>= fun ((value, g), ambient) =>
      Except.ok (value, {w with wg := g, ambient})) = _
  rw [source_jitter_exhausted site rejected bad w.wg w.ambient records]
  rfl

end Leanux.Proofs.WG.TimerDiscipline
