import Leanux.Proofs.WG.Index.StagedObservation

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setKeypair_staging (id : KeypairId) (k : Keypair) (entry : WGWorld) :
    Ensures (setKeypair id k) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  exact staging_modifyDev entry _ (fun _ => rfl) (fun _ => rfl)

theorem peerGet_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (peerGet pid) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  have counter := staging_counter_snapshot _ (Keypairs.WGFrames.peerGet_sameSnapshot pid)
    g final ambient after result run
  cases device : g.dev with
  | none =>
    simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident)
        g ambient result final after device run).1
      apply stagingFrame_of_views entry g final ?_ ?_ counter pre
      · simp [effect,device,Config.withPeer,TimerDiscipline.tableCursor]
      · rw [effect,device]
        exact stagingPeerMap_write d pid p _ resident rfl

theorem keypairGet_staging (key : Option KeypairId) (entry : WGWorld) :
    Ensures (keypairGet key) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  have counter := staging_counter_snapshot _ (Keypairs.keypairGet_sameSnapshot key)
    g final ambient after result run
  cases key with
  | none =>
    simp [keypairGet,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre
  | some id =>
    cases device : g.dev with
    | none =>
      simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some k =>
        have effect := Config.keypairGet_present id d k resident
          g ambient result final after device run
        by_cases zero : k.refcount = 0
        · simp only [zero,ite_true] at effect
          apply stagingFrame_of_views entry g final ?_ ?_ counter pre
          · rw [effect.2,device]
          · rw [effect.2,device]
        · simp only [zero,ite_false] at effect
          apply stagingFrame_of_views entry g final ?_ ?_ counter pre
          · rw [effect.2,device]; rfl
          · rw [effect.2,device]; rfl

theorem liftSkb_staging {α : Type} (action : SkbM α) (entry : WGWorld) :
    Ensures (liftSkb action) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases executed : (action.run {txSkbs := d.txSkbs,rxSkbs := d.rxSkbs,nextSkb := d.nextSkb}).run ambient with
    | error stop =>
      simp [liftSkb,getDev,device,executed] at run
    | ok pair =>
      obtain ⟨⟨value,store⟩,inputs⟩ := pair
      simp [liftSkb,getDev,modifyDev,device,executed] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      apply stagingFrame_of_views entry g _ ?_ ?_ ?_ pre
      · rw [device]; rfl
      · rw [device]; rfl
      · rfl

theorem newTxSkb_staging (packet : DataPacket) (entry : WGWorld) :
    Ensures (newTxSkb packet) (StagingFrame entry) (fun _ => StagingFrame entry) :=
  liftSkb_staging (SkbStore.newTx packet) entry

theorem setTxSkb_staging (id : SkbId) (f : DataPacket → DataPacket) (entry : WGWorld) :
    Ensures (setTxSkb id f) (StagingFrame entry) (fun _ => StagingFrame entry) :=
  liftSkb_staging (SkbStore.setTx id f) entry

theorem freeTxSkb_staging (id : SkbId) (entry : WGWorld) :
    Ensures (freeTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) :=
  liftSkb_staging (SkbStore.freeTx id) entry

theorem cpumaskChooseOnline_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (cpumaskChooseOnline pid) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [cpumaskChooseOnline,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1
      all_goals
        simp [cpumaskChooseOnline,getPeer,getDev,device,resident,invalid,branch,AmbientM.branch,
          Nat.mod_one,setPeer,modifyDev] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      · apply stagingFrame_of_views entry g _ ?_ ?_ ?_ pre
        · rw [device]; rfl
        · rw [device]; exact stagingPeerMap_write d pid p _ resident rfl
        · rfl
      · exact pre

theorem ipTunnelEcnEncap_wg_variant (P : WGWorld → Prop) (pkt : Packet) :
    ⦃fun g => ⌜P g⌝⦄ ipTunnelEcnEncap pkt ⦃⇓? _ g => ⌜P g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases bytes : pkt.bytes with
  | nil =>
    simp [ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol, bytes, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | cons byte rest =>
    by_cases ipv4 : byte.toNat / 16 = 4
    · simp [ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol, bytes, ipv4,
        ETH_P_IP, ETH_P_IPV6, ETH_P_8021Q, ETH_P_8021AD, branch, AmbientM.branch] at run
      split at run <;> rcases run with ⟨⟨rfl, rfl⟩, rfl⟩ <;> exact pre
    · by_cases ipv6 : byte.toNat / 16 = 6
      · simp [ipTunnelEcnEncap, ipTunnelGetDsfield, Packet.protocol, bytes, ipv6,
          ETH_P_IP, ETH_P_IPV6, ETH_P_8021Q, ETH_P_8021AD, branch, AmbientM.branch] at run
        split at run <;> rcases run with ⟨⟨rfl, rfl⟩, rfl⟩ <;> exact pre
      · simp [ipTunnelEcnEncap, Packet.protocol, bytes, ipv4, ipv6, invariant, AmbientM.invariant] at run
        cases run

namespace Product

theorem ipTunnelEcnEncap_kernel_variant (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ liftWG (ipTunnelEcnEncap pkt)
      ⦃⇓? _ w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w result final pre run
  change (((ipTunnelEcnEncap pkt).run w.wg).run w.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {w with wg := current, ambient := inputs})) = .ok (result, final) at run
  cases native : ((ipTunnelEcnEncap pkt).run w.wg).run w.ambient with
  | error err => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [native] at run
    cases run
    exact ((ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant (fun g => P g w.fs w.tasks w.seccomp) pkt))
      w.wg w.ambient _ current inputs pre native
end Product


theorem newTxSkbs_staging (packets : List DataPacket) (entry : WGWorld) :
    Ensures (packets.mapM newTxSkb) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  have loop (xs : List DataPacket) (acc : List SkbId) :
      Ensures (List.mapM.loop newTxSkb xs acc) (StagingFrame entry) (fun _ => StagingFrame entry) := by
    induction xs generalizing acc with
    | nil => intro _ _ _ _ _ pre run; cases run; exact pre
    | cons x xs ih =>
      unfold List.mapM.loop
      exact ensures_bind _ _ (newTxSkb_staging x entry) (fun id => ih (id::acc))
  exact loop packets []

theorem enqueuePerDeviceAndPeer_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    Ensures (enqueuePerDeviceAndPeer pid item) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  let P := StagingFrame entry
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro _ _ _ _ _ pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d => simp [getDev,device] at run; obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run; exact pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) P (fun _ => P) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .encryptWorker : WG.M Unit) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .encryptWorker) P)
  unfold enqueuePerDeviceAndPeer
  cases first : item.head? with
  | none => intro _ _ _ _ _ _ run; cases run
  | some id =>
    refine ensures_bind _ _ (setTxSkb_staging id _ entry) ?_
    intro _
    refine staging_read_bind entry pid _ _ ?_
    intro peer tag
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro full
    cases full with
    | true => exact hpure _
    | false =>
      refine ensures_bind _ _ (staging_setPeer entry pid _ tag) ?_
      intro _
      refine ensures_bind _ _ hdev ?_
      intro device
      refine ensures_bind _ _ (hcpu _) ?_
      intro cpu
      refine ensures_bind _ _ (staging_modifyDev entry _ (fun _ => rfl) (fun _ => rfl)) ?_
      intro _
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro full
      cases full with
      | true => exact hpure _
      | false =>
        refine ensures_bind _ _ hqueue ?_
        intro _
        exact ensures_bind _ _ (staging_modifyDev entry _ (fun _ => rfl) (fun _ => rfl))
          (fun _ => hpure _)

theorem setKeypair_tables (id : KeypairId) (k : Keypair) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setKeypair id k ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (setKeypair_staging id k))

theorem peerGet_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ peerGet pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (peerGet_staging pid))

theorem keypairGet_tables (key : Option KeypairId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairGet key ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (keypairGet_staging key))

theorem liftSkb_tables {α : Type} (action : SkbM α) :
    Ensures (liftSkb action) TablesSafeWG (fun _ => TablesSafeWG) :=
  staging_tables _ (liftSkb_staging action)

theorem newTxSkb_tables (packet : DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ newTxSkb packet ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (newTxSkb_staging packet))

theorem setTxSkb_tables (id : SkbId) (f : DataPacket → DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setTxSkb id f ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (setTxSkb_staging id f))

theorem freeTxSkb_tables (id : SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ freeTxSkb id ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (freeTxSkb_staging id))

theorem cpumaskChooseOnline_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ cpumaskChooseOnline pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (cpumaskChooseOnline_staging pid))

theorem newTxSkbs_tables (packets : List DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ packets.mapM newTxSkb ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (newTxSkbs_staging packets))

theorem enqueuePerDeviceAndPeer_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerDeviceAndPeer pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (enqueuePerDeviceAndPeer_staging pid item))

end Leanux.Proofs.WG.Index
