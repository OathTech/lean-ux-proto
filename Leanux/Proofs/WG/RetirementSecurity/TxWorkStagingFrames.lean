import Leanux.Proofs.WG.RetirementSecurity.TxActorCryptAhead

/-! Pre-allocation staging retains existing TX service obligations. The
key refusal path may release references; its exact queue, packet, ring and
work frames are used instead of assuming the whole world is unchanged. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) (work : SameView queued action) :
    Preserves (Obligations crypt tx) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields:=(ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run
  exact before.frame ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)
    (congrArg Prod.snd fields) (crypt_items_eq (congrArg Prod.fst fields))
    ((ProjectedAction.iff_run_ambient _ _ _).mp work w a result v b run)

theorem key_get_work (kid : Option KeypairId) : SameView queued (keypairGet kid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' tx_work_step initial

theorem no_key_work (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    SameView queued (stagedOutNokey pid packets kid invalid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairPut; exact (key_put _ _).wp (·=initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_work _ _).wp (·=initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w=>queued w=initial)
       intro x state
       change Preserves (fun w=>queued w=initial) _)
    | tx_work_step initial

theorem key_get_service (kid : Option KeypairId) : Preserves (Obligations crypt tx) (keypairGet kid) :=
  passive (keyGet_cryptWire kid) (keyGet_tx_queues kid) (key_get_work kid)

theorem no_key_service (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Obligations crypt tx) (stagedOutNokey pid packets kid invalid) :=
  passive (noKey_cryptWire pid packets kid invalid) (noKey_tx_queues pid packets kid invalid)
    (no_key_work pid packets kid invalid)

def StageReady (locals : List TxLocalBatch) (crypt : List (List SkbId)) (tx : List PeerId) (w : WGWorld) :=
  Obligations crypt tx w ∧ CryptStaging.Ready locals crypt w

theorem stage_join {action : WG.M α}
    (service : Preserves (Obligations crypt tx) action)
    (ready : Preserves (CryptStaging.Ready locals crypt) action) :
    Preserves (StageReady locals crypt tx) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp service w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp ready w a result v b before.2 run⟩

theorem stage_key_get (kid : Option KeypairId) : Preserves (StageReady locals crypt tx) (keypairGet kid) := by
  apply stage_join (key_get_service kid)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (StagingOccurrences.key_get_ready kid) w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (crypt_key_get kid) w a result v b before.2 run⟩

theorem stage_no_key (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves (StageReady locals crypt tx) (stagedOutNokey pid packets kid invalid) := by
  apply stage_join (no_key_service pid packets kid invalid)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (StagingOccurrences.no_key_ready pid packets kid invalid)
      w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (crypt_no_key pid packets kid invalid) w a result v b before.2 run⟩

theorem set_key_wire (kid : KeypairId) (value : Keypair) : SameView txCryptWire (setKeypair kid value) := by
  intro initial
  change Preserves (fun w=>txCryptWire w=initial) _
  unfold setKeypair
  repeat' crypt_wire_step initial

theorem set_key_queues (kid : KeypairId) (value : Keypair) : SameView handoffTxView (setKeypair kid value) := by
  intro initial
  change Preserves (fun w=>handoffTxView w=initial) _
  unfold setKeypair
  repeat' crypt_queue_step initial

theorem stage_set_key (kid : KeypairId) (value : Keypair) :
    Preserves (StageReady locals crypt tx) (setKeypair kid value) := by
  apply stage_join
  · apply passive (set_key_wire kid value) (set_key_queues kid value)
    exact modify _ (fun _=>rfl)
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    have ready : Preserves (StagingOccurrences.Ready locals) (setKeypair kid value) := by
      apply StagingOccurrences.frame_ready
      · intro initial
        apply hoare_modify
        intro w before
        cases hd : w.dev <;>
          simpa only [StagingOccurrences.geometry,Packets.snapshot,Packets.deviceStore,TxDisposition.txPackets,
            hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] using before
      · apply StagingOccurrences.key_frame
        intro initial
        unfold setKeypair
        repeat' holder_prepare_step initial
    exact ⟨(hoare_iff_run_ambient _ _ _).mp ready w a result v b before.1 run,
      (hoare_iff_run_ambient _ _ _).mp (crypt_passive (set_key_wire kid value) (set_key_queues kid value))
        w a result v b before.2 run⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork
