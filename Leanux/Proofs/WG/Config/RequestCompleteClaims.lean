import Leanux.Proofs.WG.Config.RequestTerminalClaims
import Leanux.Proofs.WG.Config.RequestScalarReadbackClaims

/-! Exhaustive normal request outcomes and their source-derived scalar effects.
The rejected and refused-port alternatives remain explicit. Key-stage paths
include later negative peer returns. No stopped final state or totality claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Queues Queues.RxCredits
open FinalHeader GetterScalar.Expectation

def RefusedPortResult (attrs : DeviceAttrs) (before : Device)
    (initial : Campaign2.Snapshot) (port : Nat) (ret : Int)
    (final : Campaign2.Snapshot) : Prop :=
  ret=(portOutcome (prefixDevice attrs before) port initial.wg.portBound).1 ∧
    final.wg.device.map withoutPeers=some (withoutPeers (prefixDevice attrs before)) ∧
    ClaimView.clearedPeers before final.wg.toCore before.peerList ∧
    final.wg.portBound=initial.wg.portBound ∧
    final.wg.nlSock7=initial.wg.nlSock7 ∧
    final.wg.fixtureNetDevices=initial.wg.fixtureNetDevices

def NormalScalarResult (attrs : DeviceAttrs) (before : Device)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (ret : Int) (final : Campaign2.Snapshot) : Prop :=
  (result.receipts=[] ∧ final.wg=initial.wg) ∨
  (∃port r,attrs.listenPort=some port ∧ port≠0 ∧
    r∈result.receipts ∧ r.kind=.port port ∧ r.result≠0 ∧
    ret=r.result ∧ final.wg=r.after.wg ∧
    RefusedPortResult attrs before initial port ret final) ∨
  ∃key∈result.receipts,key.kind=.keyStage ∧
    ∃current,final.wg.device=some current ∧
      Fields attrs before current ∧ PortSelected attrs before current.incomingPort ∧
      current.staticIdentity.staticPrivate=requestedPrivate attrs before ∧
      ∃actions,ReceiptSteps (peerReceipts result.receipts) actions ∧
        Agrees (fold (GetterScalar.observation initial) actions) (GetterScalar.observation final)

theorem certificate_normal_scalar_result (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (before : Device)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (device : initial.wg.device=some before)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final)) :
    NormalScalarResult attrs before initial result ret final := by
  rcases certificate_normal_cases attrs initial result certificate before device ret final normal with
    empty | refused | ⟨key,member,kind⟩
  · exact Or.inl empty
  · obtain ⟨port,r,selected,nonzero,member,kind,refused,code,state⟩:=refused
    exact Or.inr (Or.inl ⟨port,r,selected,nonzero,member,kind,refused,code,state,
      certificate_initial_port_refusal attrs initial result certificate ret final normal
        before device r member port kind nonzero refused⟩)
  · obtain ⟨current,present,_,_⟩:=certificate_final_fields attrs initial result certificate
      ret final normal key member kind before device
    obtain ⟨fields,port,privateValue⟩:=certificate_requested_private cs loans attrs initial result
      certificate pre ret final normal key member kind before device current present
    exact Or.inr (Or.inr ⟨key,member,kind,current,present,fields,port,privateValue,
      certificate_initial_final_fold cs loans attrs initial result certificate pre
        ret final normal key member kind⟩)

theorem original_request_complete_scalars (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (before : Device) :
    Campaign2.Observes (wgSetDevice attrs)
      (fun initial=>OwnerConfiguration.ProjectedEntry cs loans initial ∧ initial.wg.device=some before)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ ∀ret final,result.outcome=.ok (ret,final)→
          NormalScalarResult attrs before initial result ret final) := by
  intro g a pre
  have certificate:=inspection_certificate attrs g a
  refine ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,?_⟩
  intro ret final normal
  exact certificate_normal_scalar_result cs loans attrs before _ _ certificate
    pre.1 pre.2 ret final normal

end Leanux.Proofs.WG.Config.RequestOrder
