import Leanux.Proofs.WG.RetirementSecurity.HolderHandshakePeerFrames
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker
import Leanux.Proofs.WG.Queues.HandshakeAfterMac

/-! Concrete handshake receive boundaries combine the independent native
allocation/session support with exact key credit. Selected continuations
retain the consumer's own nonfinal peer acquisition. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits StackOwnership HolderConsume
variable {selected : PeerId}

def Ready (temporary : Credits.Ledger) (w : WGWorld) :=
  ReceiveEntry.Ready temporary w ∧ HandshakeEntry.Entry w

def Selected (temporary : Credits.Ledger) (pid : PeerId) (w : WGWorld) :=
  Ready temporary w ∧ Strong pid w

def Acquired (temporary : Credits.Ledger) (result : Option PeerId) (w : WGWorld) :=
  Ready temporary w ∧ ∀ pid,result=some pid → Strong pid w

theorem combine {action : WG.M α}
    (keys : Preserves (ReceiveEntry.Ready temporary) action)
    (entry : Preserves HandshakeEntry.Entry action) : Preserves (Ready temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp keys w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp entry w a result v b before.2 run⟩

theorem select_frame {action : WG.M α} (ready : Preserves (Ready temporary) action)
    (peers : SameView peerView action) : Preserves (Selected temporary selected) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp ready w a result v b before.1 run,
    before.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp peers w a result v b run)⟩

theorem consume (msg : List UInt8) (response : Bool) : Hoare
    (if response then consumeResponse msg else consumeInitiation msg)
    (Ready temporary) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases response with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at run
    have own := (hoare_iff_run_ambient _ _ _).mp (initiation_acquired msg) w a result v b before.1.1 run
    exact ⟨⟨⟨own.1,Allocated.native (HandshakeCall.erases (.consumeInitiation msg))
      (HandshakeCall.allocation (.consumeInitiation msg)) before.1.2 a b run⟩,
      (hoare_iff_run_ambient _ _ _).mp (HandshakeEntry.initiation msg) w a result v b before.2 run⟩,own.2⟩
  | true =>
    simp only [ite_true] at run
    have own := (hoare_iff_run_ambient _ _ _).mp (response_acquired msg) w a result v b before.1.1 run
    exact ⟨⟨⟨own.1,Allocated.native (HandshakeCall.erases (.consumeResponse msg))
      (HandshakeCall.allocation (.consumeResponse msg)) before.1.2 a b run⟩,
      (hoare_iff_run_ambient _ _ _).mp (HandshakeEntry.response msg) w a result v b before.2 run⟩,own.2⟩

theorem endpoint_points (pid : PeerId) (src : SkbSource) :
    SameView ownershipPointView (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => ownershipPointView w=initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (ownershipPoints_kernel _ (endpointFromSkb_sameWGStore _)).wp (·=initial))
    | (rx_retention_head setPeerEndpoint; exact (endpoint_ownership _ _).wp (·=initial))
    | ownership_source_step initial

theorem endpoint (pid : PeerId) (src : SkbSource) : Preserves (Selected temporary selected) (setPeerEndpointFromSkb pid src) :=
  select_frame (combine
    (HolderResponse.points (HandshakeReceiveCall.erases (.endpoint pid src))
      (HandshakeReceiveCall.allocation (.endpoint pid src)) (endpoint_points pid src))
    (HandshakeEntry.endpoint pid src)) (endpoint_peers pid src)

theorem session (pid : PeerId) : Preserves (Selected temporary selected) (beginSession pid) :=
  select_frame (combine (HolderResponse.session pid) (HandshakeReceiveSlots.session pid)) (session_peers pid)

theorem send_response (pid : PeerId) : Preserves (Selected temporary selected) (sendHandshakeResponse pid) :=
  select_frame (combine (HolderResponse.response pid) (HandshakeReceiveSlots.sendResponse pid)) (send_response_peers pid)

theorem derived (pid : PeerId) : Preserves (Selected temporary selected) (timersSessionDerived pid) :=
  select_frame (combine (HolderResponse.derived pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.derived) pid))
    (derived_peers pid)

theorem complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Selected temporary selected) (timersHandshakeComplete pid site) :=
  select_frame (combine
    (HolderResponse.points (timersHandshakeCompletePrefix_erases pid site)
      (AmbientContracts.drop (timersHandshakeCompletePrefix_spec allocationAmbient (fun _ => True) pid site))
      (handshakeComplete_ownership pid site))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.complete) pid site))
    (control_peers (timersHandshakeComplete_control pid site))

theorem keepalive (pid : PeerId) : Preserves (Selected temporary selected) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have held := (hoare_iff_run_ambient _ _ _).mp (HolderKeepalive.keepalive_selected pid) w a result v b
    ⟨⟨before.1.1.1,before.1.1.2,before.1.2.2⟩,before.2⟩ run
  exact ⟨⟨⟨held.1.1,held.1.2.1⟩,
    (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive) pid)
      w a result v b before.1.2 run⟩,held.2⟩

theorem response_session (pid : PeerId) : Preserves (Selected temporary selected) (HandshakeReceive.responseSession pid) := by
  unfold HandshakeReceive.responseSession
  simp only [branch]
  repeat' first
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.HolderReceive
