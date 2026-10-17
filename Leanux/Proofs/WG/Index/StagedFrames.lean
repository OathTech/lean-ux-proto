import Leanux.Proofs.WG.Index.ConsumeFrames
import Leanux.Proofs.WG.Config.StagedSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setKeypair_tables (id : KeypairId) (k : Keypair) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setKeypair id k
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases run
  intro final present
  cases device : g.dev with
  | none => simp [device] at present
  | some d =>
    simp only [device, Option.map_some, Option.some.injEq] at present
    subst final
    exact pre d device

theorem peerGet_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ peerGet pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [peerGet, requireNotPending, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [peerGet, requireNotPending, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident)
        g ambient result final after device run).1
      intro next present
      have same : next = Config.withPeer d pid {p with refcount := p.refcount + 1} :=
        Option.some.inj (present.symm.trans effect)
      subst next
      exact pre d device

theorem keypairGet_tables (key : Option KeypairId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairGet key ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases key with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some id =>
    cases device : g.dev with
    | none =>
      simp [keypairGet, branch, AmbientM.branch, getKeypair, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.keypairs[id]? with
      | none =>
        simp [keypairGet, branch, AmbientM.branch, getKeypair, getDev, device, found, invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        have effect := Config.keypairGet_present id d k found g ambient result final after device run
        by_cases zero : k.refcount = 0
        · simp only [zero, ite_true] at effect
          intro next present
          have same : next = d := Option.some.inj (present.symm.trans effect.2)
          subst next
          exact pre d device
        · simp only [zero, ite_false] at effect
          intro next present
          have same : next = Config.withKeypair d id {k with refcount := k.refcount + 1} :=
            Option.some.inj (present.symm.trans effect.2)
          subst next
          exact pre d device

/-- The actual component adapter still checks for a device and writes back only
its skb fields. Table safety is not a claim about the unguarded component alone. -/
private theorem liftSkb_tables {α : Type} (action : SkbM α) :
    Ensures (liftSkb action) TablesSafeWG (fun _ => TablesSafeWG) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [liftSkb, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases executed : (action.run {txSkbs := d.txSkbs, rxSkbs := d.rxSkbs, nextSkb := d.nextSkb}).run ambient with
    | error err =>
      simp [liftSkb, getDev, device, executed] at run
      cases run
    | ok pair =>
      obtain ⟨⟨value, store⟩, inputs⟩ := pair
      simp [liftSkb, getDev, modifyDev, device, executed] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      intro next present
      cases present
      exact pre d device

theorem newTxSkb_tables (packet : DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ newTxSkb packet ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (liftSkb_tables (SkbStore.newTx packet))

theorem setTxSkb_tables (id : SkbId) (f : DataPacket → DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setTxSkb id f ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (liftSkb_tables (SkbStore.setTx id f))

theorem freeTxSkb_tables (id : SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ freeTxSkb id ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (liftSkb_tables (SkbStore.freeTx id))

theorem cpumaskChooseOnline_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ cpumaskChooseOnline pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [cpumaskChooseOnline, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1
      all_goals
        simp [cpumaskChooseOnline, getPeer, getDev, device, resident, invalid, branch, AmbientM.branch,
          Nat.mod_one, setPeer, modifyDev] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        intro next present
        simp only [device, Option.some.injEq] at present
        subst next
        exact pre d device

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

theorem newTxSkbs_tables (packets : List DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ packets.mapM newTxSkb ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  have loop (xs : List DataPacket) (acc : List SkbId) :
      Ensures (List.mapM.loop newTxSkb xs acc) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing acc with
    | nil => intro g ambient result final after pre run; cases run; exact pre
    | cons x xs ih =>
      unfold List.mapM.loop
      exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (newTxSkb_tables x)) (fun id => ih (id :: acc))
  exact loop packets []

theorem enqueuePerDeviceAndPeer_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerDeviceAndPeer pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hpeer : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g ambient result final after pre run).1
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, hd] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .encryptWorker : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .encryptWorker) TablesSafeWG)
  apply (ensures_iff _ _ _).mp
  unfold enqueuePerDeviceAndPeer
  cases first : item.head? with
  | none => intro g ambient result final after pre run; cases run
  | some id =>
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ((ensures_iff _ _ _).mpr (setTxSkb_tables id _)) ?_
    intro _
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ hpeer ?_
    intro peer
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro full
    cases full with
    | true => exact hpure _
    | false =>
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
      intro _
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ hdev ?_
      intro device
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hcpu _) ?_
      intro cpu
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hmodify _ (fun _ => rfl)) ?_
      intro _
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
      intro full
      cases full with
      | true => exact hpure _
      | false =>
        refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ hqueue ?_
        intro _
        exact ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ => hpure _)

end Leanux.Proofs.WG.Index
