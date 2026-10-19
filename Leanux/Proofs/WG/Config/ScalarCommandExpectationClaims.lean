import Leanux.Proofs.WG.Config.ScalarCommandExpectationSource
import Leanux.Proofs.WG.Config.RequestOrderClaims

/-! Scalar expectations for arbitrary mixed device attributes, starting from an
actual completed key-stage cut. Normal returns identify the final WG state.
Stopped runs retain only completed-peer prefix endpoints. Expectations may retain
ghost cells for deleted peers; every actual surviving cell agrees with the fold.
No chronological per-field label, readback, or stopped final-state claim. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Queues Queues.RxCredits
open RequestOrder

theorem certificate_prefix_fold (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (expected : Map) (input : Agrees expected (observation key.after)) :
    ∃finish actions,WgLinks.Chain key.after.wg (peerReceipts result.receipts) finish ∧
      ReceiptSteps (peerReceipts result.receipts) actions ∧
      Agrees (fold expected actions) (values finish.device) := by
  obtain ⟨finish,chain⟩:=WgLinks.certificate_peer_chain attrs initial result certificate key member kind
  obtain ⟨actions,steps⟩:=certificate_steps cs loans attrs initial result certificate pre key member kind
  exact ⟨finish,actions,chain,steps,receiptSteps_advance chain steps input⟩

theorem certificate_final_fold (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (expected : Map) (input : Agrees expected (observation key.after)) :
    ∃actions,ReceiptSteps (peerReceipts result.receipts) actions ∧
      Agrees (fold expected actions) (observation final) := by
  obtain ⟨actions,steps⟩:=certificate_steps cs loans attrs initial result certificate pre key member kind
  have chain:=WgLinks.certificate_final_chain attrs initial result certificate ret final normal key member kind
  exact ⟨actions,steps,receiptSteps_advance chain steps input⟩

theorem certificate_action_position (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (actions : List Action) (steps : ReceiptSteps (peerReceipts result.receipts) actions)
    (i : Nat) (r : Receipt) (selected : (peerReceipts result.receipts)[i]?=some r) :
    ∃p action,(attrs.peers.getD [])[i]?=some (.attrs p) ∧ actions[i]?=some action ∧
      Matches p r.result r.before action ∧
      Step action (observation r.before) (observation r.after) := by
  obtain ⟨action,position,p,kind,matched,effect⟩:=receiptSteps_position steps i r selected
  exact ⟨p,action,certificate_peer_position attrs initial result certificate i r p selected kind,
    position,matched,effect⟩

theorem original_request_scalar_prefix (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (OwnerConfiguration.ProjectedEntry cs loans)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧
        ∀key∈result.receipts,key.kind=.keyStage→∀expected:Map,
          Agrees expected (observation key.after)→
          ∃finish actions,WgLinks.Chain key.after.wg (peerReceipts result.receipts) finish ∧
            ReceiptSteps (peerReceipts result.receipts) actions ∧
            Agrees (fold expected actions) (values finish.device)) := by
  intro g a pre
  have certificate:=inspection_certificate attrs g a
  refine ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,?_⟩
  intro key member kind expected input
  exact certificate_prefix_fold cs loans attrs _ _ certificate pre key member kind expected input

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
