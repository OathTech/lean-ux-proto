import Leanux.Proofs.WG.TimerDiscipline.JitterExhaustionSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- A finite rejected prefix followed by an accepted byte consumes exactly
those records. The native WireGuard state is unchanged, and only the ambient
hidden suffix changes. Arbitrary initial states and arbitrary suffixes remain. -/
theorem source_jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (g : WGWorld) (ambient : Ambient)
    (records : ambient.hidden = some (jitterStream site rejected accepted rest)) :
    ((jitterBelowRekeyTimeout site.hiddenSite).run g).run ambient =
      .ok ((jitterValue accepted, g), {ambient with hidden := some rest}) :=
  jitter_records site rejected accepted rest bad good g ambient records

/-- A finite all-rejected record stream reaches the exact missing-record
error before budget exhaustion. This includes the empty recorded stream. -/
theorem source_jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (g : WGWorld) (ambient : Ambient)
    (records : ambient.hidden = some (rejected.map (jitterRecord site))) :
    ((jitterBelowRekeyTimeout site.hiddenSite).run g).run ambient =
      .error (.hidden s!"no record left for {site.hiddenSite.info.label}") :=
  jitter_exhausted site rejected bad g ambient records

end Leanux.Proofs.WG.TimerDiscipline
