import Leanux.Proofs.WG.Noise.DriverTagControlSource
import Leanux.Proofs.WG.Noise.DriverTagFlushCallerSource

/-! Concrete stop/down observers: every timer-drain and key-clear obligation
is discharged by the original callback contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG Leanux.Proofs.Logged

def stopObserved : Obs Unit := stopObservedWith Flush.timersStopObserved
def downObserved : Obs Unit := downObservedWith Flush.timersStopObserved

theorem stopObserved_erases : ErasesStatePrefix stopObserved WG.wgStop :=
  stopObservedWith_erases _ Flush.timersStopObserved_erases

theorem downObserved_erases : ErasesStatePrefix downObserved WG.wgDown :=
  downObservedWith_erases _ Flush.timersStopObserved_erases

theorem stopObserved_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory stopObserved :=
  stopObservedWith_preserves entry _ (Flush.timersStopObserved_preserves entry) Flush.keys_tags

theorem downObserved_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory downObserved :=
  downObservedWith_preserves entry _ (Flush.timersStopObserved_preserves entry) Flush.keys_tags

end Leanux.Proofs.WG.Noise.DriverTags.Control
