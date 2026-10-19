import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextAllocation

/-! The staged-send proof carries existing packet bounds and physical queue
residency beside the ready ciphertext projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
set_option pp.structureInstances false

abbrev Ready (locals : List TxLocalBatch) (w : WGWorld) : Prop :=
  StagingOccurrences.Ready locals w ∧ Inv w

theorem ready_join {action : WG.M α}
    (physical : Preserves (StagingOccurrences.Ready locals) action)
    (coherent : Preserves Inv action) : Preserves (Ready locals) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp coherent w a result v b before.2 run⟩

theorem ready_frame {action : WG.M α} (geometry : SameView StagingOccurrences.geometry action)
    (queues : SameView handoffTxView action) : Preserves (Ready locals) action := by
  apply ready_join
  · apply StagingOccurrences.frame_ready geometry
    intro initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run pid batches found
    exact before pid batches (by
      rw [← (ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run]
      exact found)
  · exact frame (contents_factor queues) (geometry.factor Prod.snd)

theorem ready_read_key (kid : KeypairId) : Preserves (Ready locals) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b before run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ before

theorem ready_set_key (kid : KeypairId) (key : Keypair) :
    Preserves (Ready locals) (setKeypair kid key) := by
  apply ready_frame
  · intro initial
    change Preserves (fun w => StagingOccurrences.geometry w = initial) _
    unfold setKeypair
    repeat' staging_geometry_step initial
  · intro initial
    change Preserves (fun w => handoffTxView w = initial) _
    unfold setKeypair
    repeat' crypt_queue_step initial

theorem ready_no_key (pid : PeerId) (packets : List WG.Packet)
    (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Ready locals) (stagedOutNokey pid packets kid invalid) :=
  ready_join (StagingOccurrences.no_key_ready pid packets kid invalid) (frame (contents_factor (noKey_tx_queues pid packets kid invalid))
    ((noKey_cryptWire pid packets kid invalid).factor Prod.snd))

theorem ready_key_get (kid : Option KeypairId) : Preserves (Ready locals) (keypairGet kid) :=
  ready_join (StagingOccurrences.key_get_ready kid) (frame (contents_factor (keyGet_tx_queues kid)) ((keyGet_cryptWire kid).factor Prod.snd))

theorem ready_acquire (kid : KeypairId) : Preserves (Ready locals) (Affiliation.sendAcquire kid) := by
  apply ready_frame
  · intro initial
    change Preserves (fun w => StagingOccurrences.geometry w = initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (StagingOccurrences.peer_get_geometry _).wp (· = initial))
      | staging_geometry_step initial
  · apply ownership_queues
    intro initial
    change Preserves (fun w => ownershipPointView w = initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (peerGet_ownership _).wp (· = initial))
      | ownership_source_step initial

theorem submit (pid kid : Nat) (packets : List DataPacket) :
    Hoare (stagedSubmit pid kid packets) (Ready locals) (fun _ => Inv) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  simp only [stagedSubmit,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquired,items,t,e,allocated,created⟩:=run
  have held:=(hoare_iff_run_ambient _ _ _).mp (ready_acquire kid) w a () u c before acquired
  have coherent:=allocate held.2 held.1.2 held.1.1 packets c e allocated
  cases device:u.dev with
  | some d=>
    exact create coherent (held.1.2.allocate held.1.1 device pid packets c e allocated) e b created
  | none=>
    cases packets with
    | nil=>cases allocated; simp [createData] at created; cases created
    | cons p ps=>
      simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at allocated
      obtain ⟨_,_,_,first,_⟩:=allocated
      simp [newTxSkb,liftSkb_run,device] at first

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
