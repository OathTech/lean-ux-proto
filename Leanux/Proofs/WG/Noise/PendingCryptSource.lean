import Leanux.Proofs.WG.Noise.PendingCryptFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingCrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem encryptPacket_native (key : KeypairId) (packet : DataPacket) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (encryptPacket Env.checksumHelp key packet) := by
  let P := fun w : World => NativeInv w.wg seen
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding packet.plaintext.bytes.length packet.plaintext.mtu) : Leanux.M Nat) :=
    native_product _ (fun seen => (calculateSkbPadding_sameWGWorld _ _).wp (fun w => NativeInv w seen)) seen
  have checksum (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have read : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    native_product _ (getKeypair_native key) seen
  routing_tx_source [encryptPacket] using [padding,checksum,read,ambient]

theorem encryptTail_native (item : Option (List SkbId)) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => NativeInv w.wg seen
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    native_product _ (keeps_packet (SkbStore.getTx id)) seen
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    native_product _ (keeps_packet (SkbStore.setTx id f)) seen
  have enqueue (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    native_product _ (enqueue_native xs state) seen
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := encryptPacket_native key pkt seen
  have step : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,enqueue,packet,ambient]
  have need : Preserves P (Env.condResched .encryptWorker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    exact PendingSession.native_store w.wg v.wg seen
      (congrArg (fun s : ProductStore43 => s.2.2.2)
        ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel _) w x v run)) hi
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [step,need,ambient]

theorem encrypt_iteration :
    PrefixPreserves StateInv HistorySafe RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact PrefixPreserves.bind
    (lifecycle_observed _ _ (erasesStatePrefix_lift _) encryptPoll_native)
    (fun item => PrefixPreserves.bind actual_napi_softirq
      (fun _ => mixed_observed _ _ (RxWorkers.encryptTail_erases item) (encryptTail_native item)))

theorem decryptPacket_native (packet : RxPacket) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (decryptPacket packet) := by
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) _)
  intro missing
  cases missing with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (getKeypair_native packet.keypair seen)
    intro key
    apply preserves_bind ((Origins.receiveReject_sameWGWorld key).wp (fun w => NativeInv w seen))
    intro reject
    cases reject with
    | false => exact (Origins.receiveTail_sameWGWorld packet key).wp (fun w => NativeInv w seen)
    | true =>
      simpa only [bind_assoc,ite_true,id_eq] using preserves_bind
        (key_update_native packet.keypair
          (fun k => {k with receiving := {k.receiving with isValid := false}})
          (fun _ => rfl) (fun _ => rfl) seen)
        (fun _ => preserves_pure (none : Option RxPacket))

theorem publish_native (id : SkbId) (state : PacketState) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (RxWorkers.publishSource id state) := by
  let P := fun w => NativeInv w seen
  unfold RxWorkers.publishSource
  apply preserves_bind (keeps_packet (SkbStore.getRx id) seen)
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair packet.keypair) P)
  intro pid
  apply preserves_bind (peerGet_native pid seen)
  intro _
  have read : Hoare (getPeer pid) P
      (fun p w => P w ∧ (w.dev.bind fun d => d.peers[pid]?) = some p) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v after hi run
    obtain ⟨rfl,_,d,device,resident⟩ := getPeer_normal pid w v p ambient after run
    exact ⟨hi,by simp [device,resident]⟩
  apply hoare_bind _ _ read
  intro p
  let Q := fun w => P w ∧ (w.dev.bind fun d => d.peers[pid]?) = some p
  have write : Preserves Q (setRxSkb id fun q => {q with state}) := by
    have frame : SameView (fun w : WGWorld => w.dev.bind fun d => d.peers[pid]?)
        (setRxSkb id fun q => {q with state}) := by
      intro initial
      apply hoare_liftSkb
      intro w d store hi hd
      simpa only [hd,Option.bind_some] using hi
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v after hi run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (keeps_packet (SkbStore.setRx id _) seen)
        w ambient result v after hi.1 run,
      ((ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v after run).trans hi.2⟩
  have finish : Hoare (do
      setRxSkb id fun q => {q with state}
      setPeer pid {p with napiScheduled := true}
      pure pid) Q (fun _ => P) := by
    apply hoare_bind _ _ write
    intro _
    apply hoare_bind _ _ (publish_setter pid p seen)
    intro _
    exact preserves_pure pid
  split
  · apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.invariant "a decrypted packet that is not on its peer's rx_queue") Q)
    intro _
    exact finish
  · exact finish

theorem prepare_native (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant,getRxSkb,setRxSkb]
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_native _ seen)
    | (rx_retention_head RxWorkers.publishSource; exact publish_native _ _ seen)
    | (rx_retention_head liftSkb; exact keeps_packet _ seen)
    | pending_native_step seen

theorem prepare :
    PrefixPreserves StateInv HistorySafe Origins.HistoryAdapters.prepare :=
  PendingReception.observed _ _ Origins.HistoryAdapters.localPrepare_erases prepare_native

theorem decrypt_step :
    PrefixPreserves StateInv HistorySafe RxHistory.decryptStep := by
  unfold RxHistory.decryptStep
  exact NapiSource.decrypt_preserves (fun _ _ hi => hi.2.2.distinct) prepare
    (fun pid => lifecycle_observed _ _ (peerPutMixed_erases _) (peer_keeps (some pid)))
    actual_napi_softirq actual_napi_irq_exit

theorem decrypt_iteration :
    PrefixPreserves StateInv HistorySafe RxHistory.decryptIteration := by
  unfold RxHistory.decryptIteration
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2.2.distinct) decrypt_step
  exact PrefixPreserves.bind
    (viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2.2.distinct)
      state_product_store (condResched_sameKernel _))
    (fun result => viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.2.2.distinct)
      state_product_store (fun _ => productAmbient_spec (AmbientM.branch _ result) _ (fun _ _ hi => hi)))

end Leanux.Proofs.WG.Noise.PendingCrypt
