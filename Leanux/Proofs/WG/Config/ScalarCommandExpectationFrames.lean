import Leanux.Proofs.WG.Config.ScalarCommandExpectationModel
import Leanux.Proofs.WG.Config.RequestFundedCommandsFrames

/-! Same-WG-cut account transport and unchanged account/device-presence projection
of the original command. No routing-address-shape requirement is introduced. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Queues Queues.RxCredits Noise
open Leanux.Proofs.Framing Lifetimes Std.Do
open RequestOrder


theorem input_at_receipt (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (prior : Campaign2.Snapshot) (r : Receipt)
    (valid : Valid attrs r) (pre : Input cs loans prior)
    (same : r.before.wg=prior.wg) : Input cs loans r.before := by
  obtain ⟨native,_,equal⟩:=valid
  rw [←equal] at same ⊢
  obtain ⟨⟨old,a,eq,input⟩,d,device⟩:=pre
  subst prior
  have worlds:=Index.receiveInput_world same
  change native.before=old at worlds
  refine ⟨(Index.configurationInput_snapshot cs loans native.before native.ambientBefore).mpr
    (worlds.symm ▸ input),d,?_⟩
  change native.before.dev=some d
  change old.dev=some d at device
  rw [worlds]
  exact device


end Leanux.Proofs.WG.Config.GetterScalar.Expectation
