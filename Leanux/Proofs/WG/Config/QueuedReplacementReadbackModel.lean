import Leanux.Proofs.WG.Config.GetterMetadataModel
import Leanux.Proofs.WG.Config.ReplacementCompletionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline

/-- Static getter eligibility derived after normal queued replacement. -/
def ReplacementReadbackReady (d : Device) (sock : NlSock)
    (s : Campaign2.Snapshot) : Prop :=
  ∃ out, s.wg.device=some out ∧ out.peerList=[] ∧
    sendConfiguration out=sendConfiguration d ∧ s.wg.nlSock7=sock ∧
    ClaimView.selectsDevice s d ∧ ReplaceCompletion.View.Empty s

end Leanux.Proofs.WG.Config
