import Leanux.Proofs.WG.Progress.HandshakeWorkerRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal suffix facts for complete actual handshake calls, and
strict record decrease at original receive/send worker returns. These do not
assert successful evaluation, guard adequacy or global termination. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem createInitiation_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (createInitiation_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem createResponse_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (createResponse pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (createResponse_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem beginSession_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (beginSession_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem consumeInitiation_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (consumeInitiation message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (consumeInitiation_retains records message g)
    a (value,after) b (pre ▸ tail_self records) run

theorem consumeResponse_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (consumeResponse message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (consumeResponse_retains records message g)
    a (value,after) b (pre ▸ tail_self records) run

theorem cookieMessageConsume_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (cookieMessageConsume_retains records message g)
    a (value,after) b (pre ▸ tail_self records) run

theorem sendHandshakeResponse_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeResponse pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendHandshakeResponse_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem sendHandshakeInitiation_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendHandshakeInitiation_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

theorem receiveHandshakePacket_record_suffix (records : List HiddenRecord) (message : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (receiveHandshakePacket message src)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (receiveHandshakePacket_retains records message src g)
    a (value,after) b (pre ▸ tail_self records) run

theorem receiveStep_record_suffix (records : List HiddenRecord)  :
    Campaign2.Ensures (receiveStep )
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (receiveStep_retains records  g)
    a (value,after) b (pre ▸ tail_self records) run

theorem receive_activation_record_decrease (a : Activation) (worker : a.worker=.receiveWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  exact (hoare_iff_run _ _ _).mp (receive_activation_strict a worker records)
    before value after pre run

theorem send_worker_record_decrease (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runOneSendWorker
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendWorker_strict records)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
