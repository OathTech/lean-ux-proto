import Leanux.Proofs.WG.Config.RequestTerminalEffects
import Leanux.Proofs.WG.Config.RequestKeyHeaderClaims
/-! Actual request certificates classify normal endpoints. A completed refused port is nonzero by the original entry guard, without assuming namespace permission. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem certificate_empty_wg (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome = .ok (ret,final)) (empty : result.receipts = []) :
    final.wg = initial.wg := by
  exact (show result.receipts = [] → final.wg = initial.wg from
    by simpa only [PreludeFacts,normal] using certificate.2.2) empty

theorem certificate_normal_cases (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (d : Device) (device : initial.wg.device = some d)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome = .ok (ret,final)) :
    (result.receipts = [] ∧ final.wg = initial.wg) ∨
    (∃ port r, attrs.listenPort = some port ∧ port ≠ 0 ∧
      r ∈ result.receipts ∧ r.kind = .port port ∧ r.result ≠ 0 ∧
      ret = r.result ∧ final.wg = r.after.wg) ∨
    ∃ r ∈ result.receipts, r.kind = .keyStage := by
  have path : (requestLanguage attrs).normal ret result.receipts := by
    simpa only [normal] using certificate.1.2.2.2
  rcases request_normal_cases attrs ret result.receipts path with
    empty | ⟨port,r,selected,member,kind,refused⟩ | key
  · exact Or.inl ⟨empty,certificate_empty_wg attrs initial result certificate ret final normal empty⟩
  · have nonzero : port ≠ 0 := by
      intro zero
      subst port
      have input := certificate_port_input attrs initial result certificate r member 0 kind
      obtain ⟨before,present,header,_⟩ := input.resident d device
      have permission := KeyHeader.certificate_port_permission attrs initial result
        certificate r member d device 0 selected
      have net : before.creatingNet = true :=
        (congrArg Device.creatingNet header).trans permission
      exact refused (receipt_zero_port attrs r (certificate.1.2.1 r member)
        kind before net present).1
    have tail := certificate_port_refusal attrs initial result certificate ret final normal
      r member port kind refused
    exact Or.inr (Or.inl ⟨port,r,selected,nonzero,member,kind,refused,tail⟩)
  · exact Or.inr (Or.inr key)

theorem original_normal_cases (attrs : DeviceAttrs) (d : Device) :
    Campaign2.Observes (wgSetDevice attrs) (fun s => s.wg.device = some d)
      (fun initial outcome => ∃ result : Inspection,
        result.outcome = outcome ∧ Certificate attrs initial result ∧
        ∀ ret final, result.outcome = .ok (ret,final) →
          (result.receipts = [] ∧ final.wg = initial.wg) ∨
          (∃ port r, attrs.listenPort = some port ∧ port ≠ 0 ∧
            r ∈ result.receipts ∧ r.kind = .port port ∧ r.result ≠ 0 ∧
            ret = r.result ∧ final.wg = r.after.wg) ∨
          ∃ r ∈ result.receipts, r.kind = .keyStage) := by
  intro g a pre
  refine ⟨inspection attrs g a,inspection_outcome attrs g a,
    inspection_certificate attrs g a,?_⟩
  intro ret final normal
  exact certificate_normal_cases attrs (Campaign2.snapshot g a)
    (inspection attrs g a) (inspection_certificate attrs g a) d pre ret final normal
end Leanux.Proofs.WG.Config.RequestOrder
