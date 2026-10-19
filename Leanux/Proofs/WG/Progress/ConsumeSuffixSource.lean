import Leanux.Proofs.WG.Progress.EndpointSuffixSource
import Leanux.Proofs.WG.Progress.AllowedLookupSuffixSource
import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource

/-! Concrete suffix preservation for the complete original consumeDataDone. The established completion rule is instantiated with actual endpoint, confirmation, timer, staging and allowed-IP operations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem rxFinish_retains (records : List HiddenRecord) (pid : PeerId) (ready : Packets.RxReady) :
    NativeKeeps records (Packets.rxFinish pid ready) :=
  Completion.finish_retains records pid ready (lookupRepay_retains records ready.protocol ready.bytes)

theorem consumeAfterConfirmation_retains (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    NativeKeeps records (ConsumeConfirmation.afterConfirmation pid pkt confirmed) :=
  Completion.after_retains records pid pkt confirmed
    (timersComplete_retains records pid .walltimeLastHandshakeData)
    (staged_retains records pid) (prepareRest_retains records pid pkt)
    (fun ready=>rxFinish_retains records pid ready)

theorem consumeDataDone_retains (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    NativeKeeps records (consumeDataDone pid pkt ep) := by
  rw [ConsumeConfirmation.source]
  exact native_bind records _ _ (setPeerEndpoint_retains records pid ep) (fun _=>
    native_bind records _ _ (confirmation_retains records pid pkt.keypair)
      (consumeAfterConfirmation_retains records pid pkt))

end Leanux.Proofs.WG.Progress.RecordSuffix
