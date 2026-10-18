import Leanux.Proofs.WG.Index.CryptCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem key_update (kid : KeypairId) (f : Keypair → Keypair)
    (same : ∀ k, StagingRich.KeyCell (f k)=StagingRich.KeyCell k) :
    Preserves Reached.Core (do let k ← getKeypair kid; setKeypair kid (f k)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,u,c,read,write⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ := KeyTimes.getKeypair_return kid w u k a c read
  subst u
  subst c
  have cell : StagingRich.keyMap w kid=some (StagingRich.KeyCell (f k)) := by
    simp [StagingRich.keyMap,device,resident,same]
  have rich := StagingRich.setKey w kid (f k) cell w a result v b
    (StagingRich.refl w) write
  have handoff : Handoff w v [] [] {} := by
    apply handoff_of_view
    exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (modifyDev_protect (fun d => {d with keypairs := d.keypairs.insert kid (f k)})
        (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)) w a result v b write
  exact StagingRich.core_handoff rich handoff pre

theorem decryptPacket_core (packet : RxPacket) :
    Preserves Reached.Core (decryptPacket packet) := by
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) Reached.Core)
  intro missing
  cases missing with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind
    · apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a k v b pre run
      exact (KeyTimes.getKeypair_return packet.keypair w v k a b run).1 ▸ pre
    · intro k
      apply preserves_bind ((Origins.receiveReject_sameWGWorld k).wp Reached.Core)
      intro rejected
      cases rejected with
      | false => exact (Origins.receiveTail_sameWGWorld packet k).wp Reached.Core
      | true =>
        simpa only [bind_assoc,ite_true,id_eq] using preserves_bind
          (key_update packet.keypair
            (fun k => {k with receiving := {k.receiving with isValid:=false}}) (fun _=>rfl))
          (fun _ => (preserves_pure (none : Option RxPacket)))

theorem publication_middle_core (pid : PeerId) (id : SkbId) (state : PacketState) :
    Preserves Reached.Core (Queues.RxCredits.publicationMiddle pid id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  unfold Queues.RxCredits.publicationMiddle at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,tail⟩ := run
  obtain ⟨sameWorld,sameTime,d,device,resident⟩ := getPeer_normal pid w u p a c read
  subst u
  subst c
  cases contains : p.rxQueue.all.contains id with
  | false =>
    simp only [contains,Bool.not_false,ite_true] at tail
    cases tail
  | true =>
    simp only [contains,Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,updated,midway,packet,written⟩ := tail
    have mid := (hoare_iff_run_ambient _ _ _).mp
      (skb_peer (SkbStore.setRx id (fun q=>{q with state})) pid p)
      w a ignored updated midway ⟨pre,by simp [peerAt,device,resident]⟩ packet
    exact (hoare_iff_run_ambient _ _ _).mp (saved_peer pid p {p with napiScheduled:=true} rfl)
      updated midway result v b mid written

theorem publish_core (id : SkbId) (state : PacketState) :
    Preserves Reached.Core (RxWorkers.publishSource id state) := by
  rw [DecryptCarrier.publish_factor]
  apply preserves_bind (skb (SkbStore.getRx id))
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair packet.keypair) Reached.Core)
  intro pid
  apply preserves_bind (ConfigurationIndex.acquire_core pid)
  intro _
  exact preserves_bind (publication_middle_core pid id state) (fun _ => preserves_pure pid)

theorem prepare_core : Preserves Reached.Core RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta:=false}) only [branch,invariant,getRxSkb,setRxSkb]
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_core _)
    | (rx_retention_head RxWorkers.publishSource; exact publish_core _ _)
    | (rx_retention_head liftSkb; exact skb _)
    | (rx_retention_head getDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b pre run
       cases device : w.dev <;> simp [getDev,device,invariant,AmbientM.invariant] at run
       · cases run
       · obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run; exact pre)
    | (rx_retention_head modifyDev; exact ConfigurationIndex.frame_core (ConfigurationIndex.modifyDev_fields _ (fun _=>rfl)))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Index.CryptCore
