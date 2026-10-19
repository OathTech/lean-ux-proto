import Leanux.Proofs.WG.RetirementSecurity.TxWorkStaging

/-! Original staged allocation, creation and refusal retain the scheduler's
suspended actors. Only native ambient operations occurring on this path are
admitted by these frame proofs. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem key_get (kid : Option KeypairId) : Keeps (keypairGet kid) := by
  suspension_source [keypairGet,refcountIncNotZero] using [branch,compare,key,set_key,unsupported,invariant]

theorem device_work (worker : Worker) : Keeps (queueDeviceWork worker : WG.M Unit) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.queueDeviceWork at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail
  · rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨flag,u,peek,tail⟩:=tail
    have same:=(ProjectedAction.iff_run _ _ _).mp (peek_queued_ambient worker 0) w flag u peek
    cases flag <;> simp only [Bool.false_eq_true,ite_false,ite_true] at tail
    · cases tail; exact same
    · cases tail
  · rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,u,recorded,tail⟩:=tail
    have same:=(ProjectedAction.iff_run _ _ _).mp (record_queued_ambient worker 0) w () u recorded
    cases tail
    exact same

theorem cpu_next (previous : Int) : Keeps (cpumaskNextOnlineFrom previous) := by
  suspension_source [cpumaskNextOnlineFrom] using [branch,compare]

theorem admission (pid : PeerId) (items : List SkbId) : Keeps (enqueuePerDeviceAndPeer pid items) := by
  suspension_source [enqueuePerDeviceAndPeer] using [invariant,set_packet,peer,set_peer,device,
    cpu_next,modify_device,branch,device_work]

theorem create (pid : PeerId) (items : List SkbId) : Keeps (createData pid items) := by
  suspension_source [createData] using [invariant,peer,branch,admission,publish,key_put,packet,peer_put,free_packet]

theorem allocate_packet (pkt : DataPacket) : Keeps (newTxSkb pkt) := by
  apply skb_lift
  suspension_source [SkbStore.newTx] using []

theorem allocate_packets (packets : List DataPacket) : Keeps (packets.mapM newTxSkb) := by
  induction packets with
  | nil=>exact pure []
  | cons pkt rest ih=>
    rw [List.mapM_cons]
    exact bind (allocate_packet pkt) (fun item=>bind ih (fun items=>pure (item::items)))

theorem send_acquire (kid : KeypairId) : Keeps (Affiliation.sendAcquire kid) := by
  suspension_source [Affiliation.sendAcquire] using [key,owner_deref,peer_get]

theorem submit (pid kid : Nat) (packets : List DataPacket) : Keeps (stagedSubmit pid kid packets) := by
  suspension_source [stagedSubmit] using [send_acquire,allocate_packets,create]

theorem no_key (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    Keeps (stagedOutNokey pid packets kid invalid) := by
  suspension_source [stagedOutNokey] using [invariant,key,set_key,key_put,branch,peer,set_peer,queued_handshake]

theorem ecn (pkt : WG.Packet) : Keeps (ipTunnelEcnEncap pkt) := by
  suspension_source [ipTunnelEcnEncap,Packet.protocol,ipTunnelGetDsfield] using [branch,invariant,unsupported]

theorem key_source (pid kid : Nat) (packets : List WG.Packet) : Keeps (stagedKeySource pid kid packets) := by
  suspension_source [stagedKeySource] using [key,set_key,branch,compare,expired,ecn,no_key,submit]

theorem staged (pid : PeerId) : Keeps (sendStagedPackets pid) := by
  rw [←stagedFullSource_eq]
  suspension_source [stagedFullSource] using [peer,branch,set_peer,key_get,no_key,key_source,invariant]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
