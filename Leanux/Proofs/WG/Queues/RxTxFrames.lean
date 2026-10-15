import Leanux.Proofs.WG.Queues.RxMaintenanceFrames

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
  mvcgen [cpumaskChooseOnline, hg, hs, branch]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_rxQueues (pid : PeerId) (item : List SkbId) :
    SameView rxQueues (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hp := fun id f => (setTxSkb_rxQueues id f).wp (fun t => t = s)
  have hc := fun last => (rxQueues_kernel (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (rxQueues_kernel (queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t = s)
  have hd := fun u => (txDevice_rxQueues u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hp, hc, hw, hcpu, hring, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def]

theorem enqueuePerPeerTx_rxQueues (item : List SkbId) (state : PacketState) :
    RetainsRx (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have htx := fun id => (getTxSkb_rxQueues id).wp P
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have hg := fun pid => (getPeer_rxQueues pid).wp P
  have hget := fun pid => (peerGet_rxQueues pid).wp P
  have hput := fun pid => (peerPut_rxQueues pid).wp s
  have hset := fun id f => (setTxSkb_rxQueues id f).wp P
  have hcpu := fun pid => (cpumaskChooseOnline_rxQueues pid).wp P
  have hpeek := fun pid => (rxQueues_kernel (peekQueuedUnit_sameKernel .txWorker pid)).wp P
  have hrec := fun pid => (rxQueues_kernel (recordQueued_sameKernel .txWorker pid)).wp P
  have hdev := fun pid => (txDevice_rxQueues (.work pid)).wp P
  have howner := fun o => (rxQueues_kernel (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [enqueuePerPeerTx, howner, htx, hk, hg, hget, hput, hset, hcpu, hpeek, hrec, hdev,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem createData_rxQueues (pid : PeerId) (item : List SkbId) : RetainsRx (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := (getPeer_rxQueues pid).wp P
  have ht := fun id => (getTxSkb_rxQueues id).wp P
  have hd := (enqueuePerDeviceAndPeer_rxQueues pid item).wp P
  have hp := (enqueuePerPeerTx_rxQueues item .dead).wp s
  have hk := fun id => (keypairPut_rxQueues id false).wp P
  have hr := (peerPut_rxQueues (some pid)).wp s
  have hf := fun id => (freeTxSkb_rxQueues id).wp P
  mvcgen [createData, hg, ht, hd, hp, hk, hr, hf, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (rxQueues w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
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
    have hq := (sendQueuedHandshakeInitiation_rxQueues pid false).wp s
    have hl (α β : Type) := list_view_spec rxQueues (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜ResidentsRetained s (rxQueues w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

theorem newTxSkbs_rxQueues (packets : List DataPacket) : SameView rxQueues (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact SameView.bind (newTxSkb_rxQueues p) (fun _ => SameView.bind ih (fun _ => SameView.pure _ _))

theorem sendStagedPackets_rxQueues (pid : PeerId) : RetainsRx (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have hset := fun id k => (setKeypair_rxQueues id k).wp P
  have hget := fun kp => (keypairGet_rxQueues kp).wp P
  have hp := fun pid => (peerGet_rxQueues pid).wp P
  have hout := fun packets kp invalid => (stagedOutNokey_rxQueues pid packets kp invalid).wp s
  have hput := fun kp => (keypairPut_rxQueues kp false).wp P
  have hqueue := (sendQueuedHandshakeInitiation_rxQueues pid false).wp s
  have ht := fun date => (rxQueues_kernel (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME)).wp P
  have he := fun pkt => (rxQueues_kernel (ipTunnelEcnEncap_sameKernel pkt)).wp P
  have hn := fun packets => (newTxSkbs_rxQueues packets).wp P
  have hc := fun item => (createData_rxQueues pid item).wp s
  have hl (α β : Type) := list_view_spec rxQueues (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => (rxQueues_kernel (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [hw,-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (rxQueues w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

end Leanux.Proofs.WG.Queues
