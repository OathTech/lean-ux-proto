import Leanux.Proofs.WG.Config.RequestRefusalSource
import Leanux.Proofs.WG.Config.PortSourceClaims

/-! Same-request field effects and the normal endpoint after a nonzero port return. Completed receipt effects remain available when a later stage Stops. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem receipt_clear_source (attrs : DeviceAttrs) (r : Receipt)
    (valid : Valid attrs r) (pid : PeerId) (kind : r.kind = .clearSource pid)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (entry : r.before.wg.device = some d) :
    r.result = 0 ∧ ∃ d' reset, r.after.wg.device = some d' ∧
      d' = {d with peers := d'.peers} ∧
      d'.peers[pid]? = some (clearedSource p reset) ∧
      ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]? := by
  have contract := pureMap_ensures (fun _ : Unit => (0 : Int))
    (SourceClaims.original_endpoint_source_clear pid d p resident)
  obtain ⟨_,result,post⟩ := valid.ensures kind contract entry
  exact ⟨result,post⟩

theorem receipt_nonzero_port (attrs : DeviceAttrs) (r : Receipt)
    (valid : Valid attrs r) (port : Nat) (kind : r.kind = .port port)
    (d : Device) (nonzero : port ≠ 0)
    (entry : r.before.wg.device = some d) :
    if d.incomingPort = port then r.result = 0 ∧ r.after.wg.device = some d
    else r.result = (portOutcome d port r.before.wg.portBound).1 ∧
      r.after.wg.device.map withoutPeers =
        some (withoutPeers (portOutcome d port r.before.wg.portBound).2) ∧
      ClaimView.clearedPeers d r.after.wg.toCore d.peerList :=
  valid.ensures kind (SourceClaims.original_nonzero_port_effects d port nonzero
    r.before.wg.portBound) ⟨entry,rfl⟩

theorem receipt_zero_port (attrs : DeviceAttrs) (r : Receipt)
    (valid : Valid attrs r) (kind : r.kind = .port 0)
    (d : Device) (net : d.creatingNet = true)
    (entry : r.before.wg.device = some d) :
    r.result = 0 ∧ ClaimView.zeroPortEffects d r.after :=
  valid.ensures kind (SourceClaims.original_zero_port_effects d net) entry

theorem certificate_port_refusal (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome = .ok (ret,final))
    (r : Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) (nonzero : r.result ≠ 0) :
    ret = r.result ∧ final.wg = r.after.wg := by
  have point := matches_refusal attrs entry result facts.1.1
  rw [RefusalFacts,normal] at point
  obtain ⟨code,state⟩ := point r member ⟨⟨port,kind⟩,nonzero⟩
  exact ⟨code.symm,state.symm⟩

theorem original_request_refusal_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : Inspection,
        result.outcome = outcome ∧ Certificate attrs entry result ∧ RefusalFacts result) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_certificate attrs w ambient,inspection_refusal attrs w ambient⟩

theorem certificate_clear_source (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs initial result)
    (r : Receipt) (member : r ∈ result.receipts) (pid : PeerId)
    (kind : r.kind = .clearSource pid) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : r.before.wg.device = some d) :
    r.result = 0 ∧ ∃ d' reset, r.after.wg.device = some d' ∧
      d' = {d with peers := d'.peers} ∧
      d'.peers[pid]? = some (clearedSource p reset) ∧
      ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]? :=
  receipt_clear_source attrs r (facts.1.2.1 r member)
    pid kind d p resident entry

theorem certificate_nonzero_port_effects (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs initial result)
    (r : Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) (d : Device) (nonzero : port ≠ 0)
    (entry : r.before.wg.device = some d) :
    if d.incomingPort = port then r.result = 0 ∧ r.after.wg.device = some d
    else r.result = (portOutcome d port r.before.wg.portBound).1 ∧
      r.after.wg.device.map withoutPeers =
        some (withoutPeers (portOutcome d port r.before.wg.portBound).2) ∧
      ClaimView.clearedPeers d r.after.wg.toCore d.peerList :=
  receipt_nonzero_port attrs r (facts.1.2.1 r member)
    port kind d nonzero entry

theorem certificate_zero_port_effects (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs initial result)
    (r : Receipt) (member : r ∈ result.receipts) (kind : r.kind = .port 0)
    (d : Device) (net : d.creatingNet = true) (entry : r.before.wg.device = some d) :
    r.result = 0 ∧ ClaimView.zeroPortEffects d r.after :=
  receipt_zero_port attrs r (facts.1.2.1 r member)
    kind d net entry

theorem certificate_nonzero_port_refusal (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome = .ok (ret,final))
    (r : Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) (d : Device) (nonzero : port ≠ 0)
    (entry : r.before.wg.device = some d) (refused : r.result ≠ 0) :
    ret = (portOutcome d port r.before.wg.portBound).1 ∧
      final.wg.device.map withoutPeers =
        some (withoutPeers (portOutcome d port r.before.wg.portBound).2) ∧
      ClaimView.clearedPeers d final.wg.toCore d.peerList := by
  obtain ⟨code,state⟩ := certificate_port_refusal attrs initial result facts ret final normal
    r member port kind refused
  have effects := certificate_nonzero_port_effects attrs initial result facts r member
    port kind d nonzero entry
  split at effects
  · exact False.elim (refused effects.1)
  · simpa only [code,state] using effects

end Leanux.Proofs.WG.Config.RequestOrder
