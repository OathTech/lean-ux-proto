import Leanux.Proofs.WG.Config.KeyStageSource
import Leanux.Proofs.WG.Config.RequestReceiptEffectBridge
import Leanux.Proofs.WG.Config.RequestOrderInspectionBridge

/-! Projected effects of every completed private-key-stage branch. These
contracts do not require an established identity, absent collision or empty work
queues. Receipt contracts require the account at their actual stage-entry cut. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration
theorem original_stage (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (before : Device) :
    Campaign2.Ensures (RequestOrder.keyStage attrs)
      (fun s=>ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>ret=0 ∧ ProjectedEntry cs loans s ∧
        ∃ after,s.wg.device=some after ∧ Effect attrs before after) := by
  intro g a ret v b pre run
  have input := (entry_snapshot cs loans g a).mp pre.1
  obtain ⟨code,post,after,device,effect⟩ :=
    stage_effect cs loans attrs before g a ret v b ⟨input,pre.2⟩ run
  exact ⟨code,(entry_snapshot cs loans v b).mpr post,after,device,effect⟩

theorem receipt_effect (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (r : RequestOrder.Receipt) (valid : RequestOrder.Valid attrs r)
    (kind : r.kind=.keyStage) (before : Device)
    (pre : ProjectedEntry cs loans r.before) (device : r.before.wg.device=some before) :
    r.result=0 ∧ ProjectedEntry cs loans r.after ∧
      ∃ after,r.after.wg.device=some after ∧ Effect attrs before after :=
  valid.ensures kind (original_stage cs loans attrs before) ⟨pre,device⟩

/-- The stage's completed effects remain attached to this same request even
when a later command Stops. The account is at the recorded stage entry. -/
theorem certificate_effect (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (before : Device) (pre : ProjectedEntry cs loans r.before)
    (device : r.before.wg.device=some before) :
    r.result=0 ∧ ProjectedEntry cs loans r.after ∧
      ∃ after,r.after.wg.device=some after ∧ Effect attrs before after :=
  receipt_effect cs loans attrs r (certificate.1.2.1 r member) kind before pre device


end Leanux.Proofs.WG.Config.KeyStage
