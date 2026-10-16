import Leanux.Proofs.WG.Queues.RxMaintenanceFrames
import Leanux.Proofs.WG.Lifetimes.TxStaging

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original staged-TX helpers retain surviving receive queues. Their cleanup
may delete a peer on malformed ownership states, so retention rather than
unconditional equality is the compositional contract. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem txDevice_rxQueues (u : TxDeviceUpdate) : SameView rxQueues (modifyDev u.apply) :=
  modifyDev_rxQueues _ (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_rxQueues (pid : PeerId) : SameView rxQueues (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_rxQueues (pid : PeerId) (item : List SkbId) :
    SameView rxQueues (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at skb
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hc := fun last => (rxQueues_kernel (cpumaskNextOnlineFrom_sameStore last)).wp (fun t => t = s)
  have hd := fun u => (txDevice_rxQueues u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  have queued : Hoare (queueDeviceWork .encryptWorker : WG.M Unit)
      (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) _
  unfold Hoare at queued
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hc, hcpu, hring,
    setTxSkb, skb, queued, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def]

theorem enqueuePerPeerTx_rxQueues (item : List SkbId) (state : PacketState) :
    RetainsRx (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at skb
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have hg := fun pid => (getPeer_rxQueues pid).wp P
  have hget := fun pid => (peerGet_rxQueues pid).wp P
  have hput := fun pid => RetainsRx.wp (peerPut_rxQueues pid) s
  have hcpu := fun pid => (cpumaskChooseOnline_rxQueues pid).wp P
  have hdev := fun pid => (txDevice_rxQueues (.work pid)).wp P
  have peek (pid : PeerId) : Hoare (peekQueuedUnit .txWorker pid : WG.M Bool)
      (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) :=
    hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) _
  have recorded (pid : PeerId) : Hoare (recordQueued .txWorker pid : WG.M Unit)
      (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) :=
    hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) _
  unfold Hoare at peek recorded
  have howner := fun o => indexOwner_peerDeref_preserves o (fun w => P (rxQueues w))
  unfold Preserves Hoare at howner
  mvcgen [enqueuePerPeerTx, howner, hk, hg, hget, hput, hcpu, hdev,
    getTxSkb, setTxSkb, skb, peek, recorded, getDev, modifyDev,
    branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem createData_rxQueues (pid : PeerId) (item : List SkbId) : RetainsRx (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at skb
  have hg := (getPeer_rxQueues pid).wp P
  have hd := (enqueuePerDeviceAndPeer_rxQueues pid item).wp P
  have hp := RetainsRx.wp (enqueuePerPeerTx_rxQueues item .dead) s
  have hk := fun id => (keypairPut_rxQueues id false).wp P
  have hr := RetainsRx.wp (peerPut_rxQueues (some pid)) s
  mvcgen [createData, hg, hd, hp, hk, hr,
    getTxSkb, freeTxSkb, skb, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (rxQueues w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

theorem stagedOutNokey_rxQueues (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsRx (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply ProjectedAction.of_wp <;> intro s
  all_goals
    let P := ResidentsRetained s
    have hg := getPeer_rx_spec P pid
    have hs := fun p => setPeer_rx_spec P pid p
    have hk := fun id => (getKeypair_rxQueues id).wp P
    have hset := fun id k => (setKeypair_rxQueues id k).wp P
    have hp := fun kp => (keypairPut_rxQueues kp false).wp P
    have hq := RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) s
    have hl (α β : Type) := list_view_spec (m := AmbientM) rxQueues (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜ResidentsRetained s (rxQueues w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

theorem sendStagedPackets_rxQueues (pid : PeerId) : RetainsRx (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at skb
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have hset := fun id k => (setKeypair_rxQueues id k).wp P
  have hget := fun kp => (keypairGet_rxQueues kp).wp P
  have hp := fun pid => (peerGet_rxQueues pid).wp P
  have hout := fun packets kp invalid => RetainsRx.wp (stagedOutNokey_rxQueues pid packets kp invalid) s
  have hput := fun kp => (keypairPut_rxQueues kp false).wp P
  have hqueue := RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) s
  have ht := fun date => (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp (fun w => P (rxQueues w))
  have he := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp (fun w => P (rxQueues w))
  have hn (packets : List DataPacket) := mapM_view_spec rxQueues P newTxSkb packets
    (fun p => skb (SkbStore.newTx p))
  have hc := fun item => RetainsRx.wp (createData_rxQueues pid item) s
  have hl (α β : Type) := list_view_spec (m := AmbientM) rxQueues (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => indexOwner_peerDeref_preserves o (fun w => P (rxQueues w))
  unfold Preserves Hoare at hw
  mvcgen [hw, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
    hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (rxQueues w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

end Leanux.Proofs.WG.Queues
