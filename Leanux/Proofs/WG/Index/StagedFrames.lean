import Leanux.Proofs.WG.Index.StagingRichFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setKeypair_staging (id : KeypairId) (k : Keypair) (entry : WGWorld) :
    Ensures (setKeypair id k) (StagingFrame entry) (fun _ => StagingFrame entry) := by
  exact staging_modifyDev entry _ (fun _ => rfl) (fun _ => rfl)

theorem peerGet_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (peerGet pid) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.peerGet_rich pid) entry

theorem keypairGet_staging (key : Option KeypairId) (entry : WGWorld) :
    Ensures (keypairGet key) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.keypairGet_rich key) entry

theorem liftSkb_staging {α : Type} (action : SkbM α) (entry : WGWorld) :
    Ensures (liftSkb action) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.liftSkb_rich action) entry

theorem newTxSkb_staging (packet : DataPacket) (entry : WGWorld) :
    Ensures (newTxSkb packet) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.newTxSkb_rich packet) entry

theorem setTxSkb_staging (id : SkbId) (f : DataPacket → DataPacket) (entry : WGWorld) :
    Ensures (setTxSkb id f) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.setTxSkb_rich id f) entry

theorem freeTxSkb_staging (id : SkbId) (entry : WGWorld) :
    Ensures (freeTxSkb id) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.freeTxSkb_rich id) entry

theorem cpumaskChooseOnline_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (cpumaskChooseOnline pid) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.cpumaskChooseOnline_rich pid) entry

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

end Leanux.Proofs.WG.Index
