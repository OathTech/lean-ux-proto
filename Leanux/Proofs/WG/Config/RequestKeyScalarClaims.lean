import Leanux.Proofs.WG.Config.RequestKeyScalarSource
import Leanux.Proofs.WG.Config.KeyScalarClaims
import Leanux.Proofs.WG.Config.RequestReceiptEffectBridge

/-! Every actual completed private-key stage retains surviving getter scalar cells from the original request entry, including receipts before a later Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration Leanux.Proofs.Logged RequestOrder

theorem matches_key_entries (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (same : Matches attrs initial result) :
    KeyEntries (Keeps initial) result.receipts := by
  obtain ⟨g,a,rfl,rfl⟩:=same
  exact EntryTransport.inspection_history _ _ attrs (prefix_contracts _ attrs) g a
    (fun _ _ found=>found)

theorem certificate_key_scalars (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage) :
    Keeps initial r.before ∧ Keeps initial r.after := by
  have before:=matches_key_entries attrs initial result certificate.1.1 r member kind
  exact ⟨before,(certificate.1.2.1 r member).ensures kind (key_stage_keeps initial attrs) before⟩

theorem original_key_scalars (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun initial outcome=>∃result : Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧
        ∀r∈result.receipts,r.kind=.keyStage → Keeps initial r.before ∧ Keeps initial r.after) := by
  intro g a _
  have certificate:=inspection_certificate attrs g a
  exact ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,
    fun r member kind=>certificate_key_scalars attrs _ _ certificate r member kind⟩
end Leanux.Proofs.WG.Config.GetterScalar
