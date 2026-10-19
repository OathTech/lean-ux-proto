import Leanux.Proofs.WG.TimerDiscipline.SendView

/-! The device header and selector context retained during configuration cleanup.
Absence stays visible: this observation does not make a separate socket claim
when the device is absent. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline

abbrev GetterMetadata := Option (SendConfiguration × SendSocketContext)

def getterMetadataObservation (s : Campaign2.Snapshot) : GetterMetadata :=
  s.wg.device.map fun d => (sendConfiguration d, s.wg.nlSock7, s.wg.fixtureNetDevices)

end Leanux.Proofs.WG.Config

