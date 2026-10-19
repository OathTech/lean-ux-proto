import Leanux.Proofs.WG.RetirementSecurity.TxWorkHandshakeSendFrames

/-! Native handshake operations retain converse TX coverage and its service
obligations. A response's keepalive enters the actual staged allocation path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem passive_contents {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView txQueueContents action) (work : SameView queued action) :
    Preserves (Obligations crypt tx) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields:=(ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run
  exact before.contents ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)
    (congrArg Prod.snd fields) (crypt_items_eq (congrArg Prod.fst fields))
    ((ProjectedAction.iff_run_ambient _ _ _).mp work w a result v b run)

theorem serving_handshake (call : HandshakeCall) : Preserves (Serving locals crypt tx) call.original := by
  apply serving_join
  · cases call with
    | createInitiation pid =>
      exact passive (OccurrenceKeys.create_initiation_wire pid)
        (OccurrenceKeys.create_initiation_queues pid) (create_initiation_work pid)
    | createResponse pid =>
      exact passive (OccurrenceKeys.create_response_wire pid)
        (OccurrenceKeys.create_response_queues pid) (create_response_work pid)
    | consumeInitiation msg =>
      exact passive_contents (OccurrenceHandshake.consume_initiation_wire msg)
        (OccurrenceHandshake.consume_initiation_contents msg) (consume_initiation_work msg)
    | consumeResponse msg =>
      exact passive_contents (OccurrenceHandshake.consume_response_wire msg)
        (OccurrenceHandshake.consume_response_contents msg) (consume_response_work msg)
    | addMac pid msg =>
      exact passive (OccurrenceKeys.add_mac_wire pid msg)
        (OccurrenceKeys.add_mac_queues pid msg) (add_mac_work pid msg)
  · exact TxCovered.join (OccurrenceHandshake.call call) (TxCoverageNative.call call)

theorem serving_handshake_send (call : HandshakeSendCall) : Preserves (Serving locals crypt tx) call.original := by
  apply serving_join
  · cases call with
    | buffer pid msg =>
      exact passive_contents (OccurrenceHandshake.buffer_wire pid msg)
        (OccurrenceHandshake.buffer_contents pid msg) (buffer_work pid msg)
    | sessionDerived pid =>
      exact passive_contents (OccurrenceHandshake.derived_wire pid)
        (OccurrenceHandshake.derived_contents pid) (derived_work pid)
    | initiated pid =>
      exact passive_contents (OccurrenceHandshake.initiated_wire pid)
        (OccurrenceHandshake.initiated_contents pid) (initiated_work pid)
    | initiation pid =>
      exact passive_contents (OccurrenceHandshake.send_initiation_wire pid)
        (OccurrenceHandshake.send_initiation_contents pid) (send_initiation_work pid)
    | response pid =>
      exact passive_contents (OccurrenceHandshake.send_response_wire pid)
        (OccurrenceHandshake.send_response_contents pid) (send_response_work pid)
    | worker pid =>
      exact passive_contents (OccurrenceHandshake.send_worker_wire pid)
        (OccurrenceHandshake.send_worker_contents pid) (send_worker_work pid)
  · exact TxCovered.join (OccurrenceHandshake.send_call call) (TxCoverageNative.send_call call)

theorem serving_session (pid : PeerId) : Preserves (Serving locals crypt tx) (beginSession pid) :=
  serving_join (passive (OccurrenceKeys.session_wire pid) (OccurrenceKeys.session_queues pid) (session_work pid))
    (TxCovered.join (OccurrenceHandshake.session pid) (TxCoverageNative.session pid))

theorem keepalive_prepare_work (pid : PeerId) : SameView queued (OccurrenceHandshake.keepalivePrepare pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold OccurrenceHandshake.keepalivePrepare
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' tx_work_step initial

theorem serving_keepalive (pid : PeerId) : Preserves (Serving locals crypt tx) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have covered:=(hoare_iff_run_ambient _ _ _).mp (TxCovered.Native.keepalive pid)
    w a result v b before.2 run
  cases result
  rw [OccurrenceHandshake.keepalive_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepared,tail⟩:=run
  have kept:=(hoare_iff_run_ambient _ _ _).mp
    (stage_frame (OccurrenceHandshake.keepalive_prepare_geometry pid)
      (OccurrenceHandshake.keepalive_prepare_wire pid)
      (OccurrenceHandshake.keepalive_prepare_queues pid) (keepalive_prepare_work pid))
    w a ready u c before.stage_ready prepared
  refine ⟨?_,covered⟩
  cases ready with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact kept.1
  | true => exact staged_service kept pid c b tail

end Leanux.Proofs.WG.RetirementSecurity.TxWork
