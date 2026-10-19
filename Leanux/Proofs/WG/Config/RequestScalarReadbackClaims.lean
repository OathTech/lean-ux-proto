import Leanux.Proofs.WG.Config.ScalarCommandExpectationClaims
import Leanux.Proofs.WG.Config.RequestKeyScalarClaims
import Leanux.Proofs.WG.Config.ConfiguredReadbackClaims

/-! Initial-entry scalar expectations and exact mixed getter composition.
Only actual surviving cells must agree with the fold. Untracked row fields
remain those of the actual final peer; this is not full-row equality. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Noise TimerDiscipline Configuration Queues Queues.RxCredits
open RequestOrder RequestOrder.FinalHeader

theorem certificate_initial_final_fold (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage) :
    ∃actions,ReceiptSteps (peerReceipts result.receipts) actions ∧
      Agrees (fold (observation initial) actions) (observation final) :=
  certificate_final_fold cs loans attrs initial result certificate pre ret final normal
    key member kind (observation initial)
    (GetterScalar.certificate_key_scalars attrs initial result certificate key member kind).2

theorem original_request_final_scalars (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (OwnerConfiguration.ProjectedEntry cs loans)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧
        ∀ret final,result.outcome=.ok (ret,final)→
          ∀key∈result.receipts,key.kind=.keyStage→
            ∃actions,ReceiptSteps (peerReceipts result.receipts) actions ∧
              Agrees (fold (observation initial) actions) (observation final)) := by
  intro g a pre
  have certificate:=inspection_certificate attrs g a
  refine ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,?_⟩
  intro ret final normal key member kind
  exact certificate_initial_final_fold cs loans attrs _ _ certificate pre
    ret final normal key member kind

theorem certificate_mixed_scalar_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (selected : ClaimView.selectsDevice initial before)
    (d : Device) (present : middle.wg.device=some d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : initial.wg.nlSock7.cbRunning=false) (emptyQueue : initial.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome) :
    (∃actions,ReceiptSteps (peerReceipts inspected.receipts) actions ∧
      Agrees (fold (observation initial) actions) (observation middle)) ∧
    (let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Fields attrs before d ∧ PortSelected attrs before d.incomingPort ∧
      d.staticIdentity.staticPrivate=requestedPrivate attrs before ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal initial.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none) := by
  constructor
  · exact certificate_initial_final_fold cs loans attrs initial inspected certificate pre
      ret middle normal r member kind
  · exact certificate_requested_mixed_readback cs loans attrs shape initial inspected
      certificate pre ret middle normal r member kind before first selected d present
      ready headerFits cursorData idle emptyQueue within outcome matched

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
