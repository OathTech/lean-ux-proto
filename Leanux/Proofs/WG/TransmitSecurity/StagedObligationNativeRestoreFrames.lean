import Leanux.Proofs.WG.TransmitSecurity.StagedObligationNativeReadyFrames

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.NativeReady
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues RetirementSecurity Queues.RxCredits

theorem put_key_queues (kid : Option KeypairId) : SameView handoffTxView (keypairPut kid false) :=
  (keypairPut_protect kid false).factor (fun fields => fields.2.2.1)

theorem put_key (kid : Option KeypairId) : Preserves (Inv locals) (keypairPut kid false) :=
  native (StagingOccurrences.key_put_geometry kid false)
    ((put_key_queues kid).factor (fun q pid => (q pid).getD []))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.NativeReady
