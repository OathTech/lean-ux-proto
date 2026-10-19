import Leanux.Proofs.WG.Config.RequestInputSource
import Leanux.Proofs.WG.Config.RequestReceiptClaims

/-! Projected whole-request port-input continuity and original-entry field effects at normal nonzero-port refusal. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem matches_input (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (matched : Matches attrs entry result) :
    InputHistory attrs entry.wg result.receipts := by
  obtain ⟨w,ambient,rfl,rfl⟩ := matched
  exact inspection_input attrs w ambient

theorem certificate_port_input (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (r : Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) : PortInput attrs entry.wg r :=
  matches_input attrs entry result facts.1.1 r member port kind

theorem original_request_input_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : Inspection,
        result.outcome = outcome ∧ Certificate attrs entry result ∧
          InputHistory attrs entry.wg result.receipts) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_certificate attrs w ambient,inspection_input attrs w ambient⟩

theorem certificate_initial_port_refusal (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome = .ok (ret,final))
    (d : Device) (entry : initial.wg.device = some d)
    (r : Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) (nonzero : port ≠ 0) (refused : r.result ≠ 0) :
    ret = (portOutcome (prefixDevice attrs d) port initial.wg.portBound).1 ∧
      final.wg.device.map withoutPeers = some (withoutPeers (prefixDevice attrs d)) ∧
      ClaimView.clearedPeers d final.wg.toCore d.peerList ∧
      final.wg.portBound = initial.wg.portBound ∧
      final.wg.nlSock7 = initial.wg.nlSock7 ∧
      final.wg.fixtureNetDevices = initial.wg.fixtureNetDevices := by
  have input := certificate_port_input attrs initial result facts r member port kind
  obtain ⟨current,resident,header,clears,context⟩ := input.resident d entry
  obtain ⟨code,state⟩ := certificate_port_refusal attrs initial result facts
    ret final normal r member port kind refused
  have effects := receipt_nonzero_port attrs r (facts.1.2.1 r member)
    port kind current nonzero resident
  split at effects
  · exact False.elim (refused effects.1)
  · have stopped : (portOutcome current port r.before.wg.portBound).1 ≠ 0 := by
      rw [← effects.1]
      exact refused
    have unchanged := portOutcome_refused current port r.before.wg.portBound stopped
    have listHeader := congrArg Device.peerList header
    have list : current.peerList = d.peerList := listHeader
    have merged : ClaimView.clearedPeers d r.after.wg.toCore d.peerList := by
      apply clearedPeers_compose d current r.after.wg.toCore
        (if attrs.fwmark.isSome then d.peerList else []) d.peerList
      · intro q seen
        split at seen
        · exact seen
        · cases seen
      · simpa only [ClaimView.clearedPeers,resident,Option.bind_some] using clears
      · simpa only [list] using effects.2.2
    have bound := receipt_nonzero_port_context attrs r (facts.1.2.1 r member) port nonzero kind
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [code,effects.1,context.1]
      exact portOutcome_code_frame current (prefixDevice attrs d) port initial.wg.portBound header
    · rw [state,effects.2.1,unchanged,header]
    · simpa only [state] using merged
    · rw [state,bound.1,context.1]
    · rw [state,bound.2.1,context.2.1]
    · rw [state,bound.2.2,context.2.2]

end Leanux.Proofs.WG.Config.RequestOrder
