import Leanux.Proofs.WG.Config.GetterMetadataModel

/-! Optional device-associated getter context. None makes no independent claim about the socket or fixture selector table. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterContext
open Leanux Leanux.WG TimerDiscipline

abbrev Context := Option SendSocketContext
def observation (s : Campaign2.Snapshot) : Context := (getterMetadataObservation s).map Prod.snd

end Leanux.Proofs.WG.Config.GetterContext
