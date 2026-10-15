import Leanux.Proofs.WG.Queues.RxRingWorker
import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Lifetimes.BatchCalls

/-! Full decrypt-ring cell frames for concrete receive callbacks. Peer/keypair
release and TX enqueue are allowed: this view retains the device index and
complete physical decrypt ring, not peer residency or packet ownership.
Source coverage of lifted helpers is separate from normal-endpoint framing. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem getPeer_cell (pid : PeerId) : SameView cell (getPeer pid) := getPeer_frame pid
theorem getKeypair_cell (id : KeypairId) : SameView cell (getKeypair id) := getKeypair_frame id
theorem keypairGet_cell (id : Option KeypairId) : SameView cell (keypairGet id) := keypairGet_frame id
theorem keypairPut_cell (id : Option KeypairId) (now : Bool) : SameView cell (keypairPut id now) := keypairPut_frame id now
theorem peerGet_cell (id : PeerId) : SameView cell (peerGet id) := peerGet_frame id
theorem peerGetMaybeZero_cell (id : Option PeerId) : SameView cell (peerGetMaybeZero id) := peerGetMaybeZero_frame id
theorem peerPut_cell (id : Option PeerId) : SameView cell (peerPut id) := peerPut_frame id

theorem getPeer_cell_spec (P : (Option (Nat × PtrRing SkbId)) → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (cell w)⌝⦄ getPeer pid ⦃⇓? _ w => ⌜P (cell w)⌝⦄ :=
  (getPeer_frame pid).wp P

theorem setPeer_cell_spec (P : (Option (Nat × PtrRing SkbId)) → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (cell w)⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜P (cell w)⌝⦄ :=
  (setPeer_frame pid p).wp P

theorem modifyPeer_cell (pid : PeerId) (f : Peer → Peer)
    (_hs : ∀ p, (f p).internalId = p.internalId) (_hq : ∀ p, (f p).rxQueue = p.rxQueue) :
    SameView cell (do let p ← getPeer pid; setPeer pid (f p)) :=
  (getPeer_frame pid).bind (fun p => setPeer_frame pid (f p))

theorem modifyDev_cell (f : Device → Device) (he : ∀ d, (f d).ifindex = d.ifindex)
    (hq : ∀ d, (f d).decryptQueue = d.decryptQueue) : SameView cell (modifyDev f) := modify f he hq

theorem cell_kernel (ha : SameKernel a) : SameView cell a := kernel ha
theorem requireNotPending_cell (pid : PeerId) (why : String) :
    SameView cell (requireNotPending pid why) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  mvcgen [requireNotPending, hg, unsupported]

theorem setKeypair_cell (kp : KeypairId) (k : Keypair) : SameView cell (setKeypair kp k) :=
  modifyDev_cell _ (fun _ => rfl) (fun _ => rfl)

theorem getTxSkb_cell (id : SkbId) : SameView cell (getTxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb, getDev, getK, invariant]

theorem setTxSkb_cell (id : SkbId) (f : DataPacket → DataPacket) :
    SameView cell (setTxSkb id f) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_cell id).wp (fun t => t = s)
  have hm := fun p => (modifyDev_cell (fun d => {d with txSkbs := d.txSkbs.insert id (f p)})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [setTxSkb, hg, hm]

theorem newTxSkb_cell (p : DataPacket) : SameView cell (newTxSkb p) := by
  apply SameView.of_wp
  intro s
  mvcgen [newTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold cell at *; simp_all

theorem freeTxSkb_cell (id : SkbId) : SameView cell (freeTxSkb id) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_cell id).wp (fun t => t = s)
  have hm := (modifyDev_cell (fun d => {d with txSkbs := d.txSkbs.erase id})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [freeTxSkb, hg, hm]


theorem counterValidate_cell (kp : KeypairId) (nonce : Nat) :
    SameView cell (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  mvcgen [counterValidate, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, WG.orM, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

  all_goals trivial

theorem receivedWithKeypair_cell (pid : PeerId) (kp : KeypairId) :
    SameView cell (receivedWithKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  have hk := fun old => (keypairPut_cell old true).wp (fun t => t = s)
  have hm (f : Peer → Peer) (hs : ∀ p, (f p).internalId = p.internalId)
      (hq : ∀ p, (f p).rxQueue = p.rxQueue) :=
    (modifyPeer_cell pid f hs hq).wp (fun t => t = s)
  have hm1 := hm (fun p => {p with keypairPrevious := p.keypairCurrent}) (fun _ => rfl) (fun _ => rfl)
  have hm2 := hm (fun p => {p with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl) (fun _ => rfl)
  have hp1 : ⦃fun w => ⌜cell w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairPrevious := p.keypairCurrent})
      ⦃⇓? _ w => ⌜cell w = s⌝⦄ := hm1
  have hp2 : ⦃fun w => ⌜cell w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent := some kp, keypairNext := none})
      ⦃⇓? _ w => ⌜cell w = s⌝⦄ := hm2
  mvcgen [receivedWithKeypair, hg, hk, hp1, hp2, branch, invariant]


theorem dstCacheReset_cell (pid : PeerId) : SameView cell (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have ht := (cell_kernel (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun t => t = s)
  mvcgen [dstCacheReset, hg, hs, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem setPeerEndpoint_cell (pid : PeerId) (e : Endpoint) : SameView cell (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hn := (requireNotPending_cell pid "changing the endpoint").wp (fun t => t = s)
  have he := fun old => (cell_kernel (endpointEq_sameKernel e old)).wp (fun t => t = s)
  have hc := (dstCacheReset_cell pid).wp (fun t => t = s)
  mvcgen [setPeerEndpoint, hg, hs, hn, he, hc, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem armTimer_cell (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView cell (armTimer pid timer delay jc) := by
  rw [armTimer_source pid timer delay jc]
  apply SameView.bind (cell_kernel (timerArmExpiry_sameKernel pid timer delay jc))
  intro expiry
  exact modifyPeer_cell pid (fun p => p.setTimer timer (some expiry))
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem delTimer_cell (pid : PeerId) (timer : PeerTimer) : SameView cell (delTimer pid timer) :=
  modifyPeer_cell pid (fun p => p.setTimer timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_cell (pid : PeerId) : SameView cell (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  mvcgen [modPeerTimerGuard, getDev, getK, hg, WG.andM, branch, invariant]

theorem modPeerTimer_cell (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView cell (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_cell pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_cell pid timer delay jc).wp (fun t => t = s)
  have hc := (cell_kernel (callerJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersHandshakeComplete_cell (pid : PeerId) (site : HiddenSite) :
    SameView cell (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (delTimer_cell pid .retransmitHandshake).wp (fun t => t = s)
  have hh := (cell_kernel (hidden_sameKernel site)).wp (fun t => t = s)
  mvcgen [timersHandshakeComplete, hg, hs, hd, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem timersAnyAuthenticatedPacketReceived_cell (pid : PeerId) :
    SameView cell (timersAnyAuthenticatedPacketReceived pid) := delTimer_cell pid .newHandshake

theorem timersDataReceived_cell (pid : PeerId) : SameView cell (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have ht := (modPeerTimer_cell .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec cell (fun t => t = s) _ ht
  mvcgen [timersDataReceived, hg, hs, ht, hd, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem timersTraversal_cell (pid : PeerId) : SameView cell (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_cell pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_cell .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec cell (fun t => t = s) _ (ht delay)
  mvcgen [timersTraversal, hg, ht, hd, branchCmp]

/-- Queueing a handshake can release the extra peer reference while preserving
the complete decrypt-ring cell; no ownership premise is imposed. -/
theorem sendQueuedHandshakeInitiation_cell (pid : PeerId) (retry : Bool) :
    SameView cell (sendQueuedHandshakeInitiation pid retry) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hn := (requireNotPending_cell pid "queueing a handshake").wp P
  have hc := fun date => (cell_kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))).wp P
  have hget := (peerGet_cell pid).wp P
  have hput := (peerPut_cell (some pid)).wp P
  have hrec := (cell_kernel (recordQueued_sameKernel .sendWorker pid)).wp P
  have hqueue := (modifyDev_cell (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl)).wp P
  mvcgen [sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hrec, hqueue, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (simp_all [cell, Option.map_map, Function.comp_def])
  all_goals try subst s
  all_goals rfl

theorem keepKeyFreshRx_cell (pid : PeerId) : SameView cell (keepKeyFreshRx pid) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hk := fun id => (getKeypair_cell id).wp P
  have ht := fun date delay => (cell_kernel (branchExpired_sameKernel .rxFreshExpired date delay)).wp P
  have hq := (sendQueuedHandshakeInitiation_cell pid false).wp P
  mvcgen [keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (simp_all [cell, Option.map_map, Function.comp_def])
  all_goals try subst s
  all_goals rfl


theorem txDevice_cell (u : TxDeviceUpdate) : SameView cell (modifyDev u.apply) :=
  modifyDev_cell _ (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_cell (pid : PeerId) : SameView cell (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold cell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_cell (pid : PeerId) (item : List SkbId) :
    SameView cell (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hp := fun id f => (setTxSkb_cell id f).wp (fun t => t = s)
  have hc := fun last => (cell_kernel (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (cell_kernel (queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t = s)
  have hd := fun u => (txDevice_cell u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hp, hc, hw, hcpu, hring, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold cell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def]

theorem enqueuePerPeerTx_cell (item : List SkbId) (state : PacketState) :
    SameView cell (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have htx := fun id => (getTxSkb_cell id).wp P
  have hk := fun id => (getKeypair_cell id).wp P
  have hg := fun pid => (getPeer_cell pid).wp P
  have hget := fun pid => (peerGet_cell pid).wp P
  have hput := fun pid => (peerPut_cell pid).wp P
  have hset := fun id f => (setTxSkb_cell id f).wp P
  have hcpu := fun pid => (cpumaskChooseOnline_cell pid).wp P
  have hpeek := fun pid => (cell_kernel (peekQueuedUnit_sameKernel .txWorker pid)).wp P
  have hrec := fun pid => (cell_kernel (recordQueued_sameKernel .txWorker pid)).wp P
  have hdev := fun pid => (txDevice_cell (.work pid)).wp P
  have hw := fun o => (cell_kernel (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [hw, enqueuePerPeerTx, htx, hk, hg, hget, hput, hset, hcpu, hpeek, hrec, hdev,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold cell at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals rfl

theorem createData_cell (pid : PeerId) (item : List SkbId) : SameView cell (createData pid item) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := (getPeer_cell pid).wp P
  have ht := fun id => (getTxSkb_cell id).wp P
  have hd := (enqueuePerDeviceAndPeer_cell pid item).wp P
  have hp := (enqueuePerPeerTx_cell item .dead).wp P
  have hk := fun id => (keypairPut_cell id false).wp P
  have hr := (peerPut_cell (some pid)).wp P
  have hf := fun id => (freeTxSkb_cell id).wp P
  mvcgen [createData, hg, ht, hd, hp, hk, hr, hf, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (cell w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold cell at *; simp_all [Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial

theorem stagedOutNokey_cell (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    SameView cell (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply SameView.of_wp <;> intro s
  all_goals
    let P := fun t => t = s
    have hg := getPeer_cell_spec P pid
    have hs := fun p => setPeer_cell_spec P pid p
    have hk := fun id => (getKeypair_cell id).wp P
    have hset := fun id k => (setKeypair_cell id k).wp P
    have hp := fun kp => (keypairPut_cell kp false).wp P
    have hq := (sendQueuedHandshakeInitiation_cell pid false).wp P
    have hl (α β : Type) := list_view_spec cell (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold cell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial

theorem newTxSkbs_cell (packets : List DataPacket) : SameView cell (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact SameView.bind (newTxSkb_cell p) (fun _ => SameView.bind ih (fun _ => SameView.pure _ _))

theorem sendStagedPackets_cell (pid : PeerId) : SameView cell (sendStagedPackets pid) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := getPeer_cell_spec P pid
  have hs := fun p => setPeer_cell_spec P pid p
  have hk := fun id => (getKeypair_cell id).wp P
  have hset := fun id k => (setKeypair_cell id k).wp P
  have hget := fun kp => (keypairGet_cell kp).wp P
  have hp := fun pid => (peerGet_cell pid).wp P
  have hout := fun packets kp invalid => (stagedOutNokey_cell pid packets kp invalid).wp P
  have hput := fun kp => (keypairPut_cell kp false).wp P
  have hqueue := (sendQueuedHandshakeInitiation_cell pid false).wp P
  have ht := fun date => (cell_kernel (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME)).wp P
  have he := fun pkt => (cell_kernel (ipTunnelEcnEncap_sameKernel pkt)).wp P
  have hn := fun packets => (newTxSkbs_cell packets).wp P
  have hc := fun item => (createData_cell pid item).wp P
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => (cell_kernel (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [hw,-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (cell w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold cell at *; simp_all [CurrentRx, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | rfl | trivial


theorem lookup_cell (root : Option NodeId) (bits key : Nat) :
    SameView cell (lookup root bits key) := by
  apply SameView.of_wp
  intro s
  have hs := (cell_kernel (swapEndian_sameKernel bits)).wp (fun t => t = s)
  have hf := (cell_kernel (findNode_sameKernel root bits key)).wp (fun t => t = s)
  have hn := fun id => (cell_kernel (Framing.getNode_sameKernel id)).wp (fun t => t = s)
  have hp := fun pid => (peerGetMaybeZero_cell pid).wp (fun t => t = s)
  mvcgen [lookup, hs, hf, hn, hp, branch, invariant, unsupported]

theorem lookupSrc_cell (protocol : Nat) (bytes : List UInt8) :
    SameView cell (lookupSrc protocol bytes) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_cell root bits key).wp (fun t => t = s)
  mvcgen [lookupSrc, hl, getDev, getK, branch, invariant]

theorem dishonest_cell (why : Dishonest) : SameView cell (dishonest why) :=
  modifyDev_cell _ (fun d => by cases why <;> rfl) (fun d => by cases why <;> rfl)

theorem updateRxStats_cell (pid : PeerId) (len : Nat) :
    SameView cell (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (modifyDev_cell (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem consumeDataDone_cell (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView cell (consumeDataDone pid pkt endpoint) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hep := (setPeerEndpoint_cell pid endpoint).wp P
  have hk := (receivedWithKeypair_cell pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_cell pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_cell pid).wp P
  have hf := (keepKeyFreshRx_cell pid).wp P
  have ha := (timersAnyAuthenticatedPacketReceived_cell pid).wp P
  have htr := (timersTraversal_cell pid).wp P
  have hdata := (timersDataReceived_cell pid).wp P
  have hstats := fun len => (updateRxStats_cell pid len).wp P
  have herr := fun why => (dishonest_cell why).wp P
  have hecn := fun protocol outer bytes => (cell_kernel (inetEcnDecapsulate_sameKernel protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_cell protocol bytes).wp P
  have hp := fun peer => (peerPut_cell peer).wp P
  mvcgen [consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold cell at *; simp_all)
  all_goals try subst s
  all_goals rfl


theorem lookupDst_cell (family addr : Nat) :
    SameView cell (lookupDst family addr) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_cell root bits key).wp (fun t => t = s)
  mvcgen [lookupDst, hl, getDev, getK, branch, invariant]

theorem xmitTrim_cell (pid : PeerId) : SameView cell (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have hd := (modifyDev_cell (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem xmitSplice_cell (pid : PeerId) (packets : List Packet) :
    SameView cell (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_cell pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl) (fun _ => rfl)

/-- Original transmit entry preserves the complete decrypt-ring cell on every
normal return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_cell (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    SameView cell (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := fun pid => (getPeer_cell pid).wp P
  have hlookup := (lookupDst_cell family addr).wp P
  have htrim := fun pid => (xmitTrim_cell pid).wp P
  have hsplice := fun pid packets => (xmitSplice_cell pid packets).wp P
  have hstage := fun pid => (sendStagedPackets_cell pid).wp P
  have hput := fun pid => (peerPut_cell pid).wp P
  have hloop := fun sites raised => (cell_kernel (loopbackSend_kernel sites raised)).wp P
  have hcut := fun sites => (cell_kernel (skipCutSites_sameKernel sites)).wp P
  have henv := fun site => (cell_kernel (envOk_sameKernel site)).wp P
  have herr := (modifyDev_cell (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, wgXmitSource,
    hg, hlookup, htrim, hsplice, hstage, hput, hloop, hcut, henv, herr,
    WG.andM, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | rfl | trivial

theorem reply4_cell (dst : Nat) (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.reply4 dst bytes) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hc := fun sites => (cell_kernel (skipCut_sameKernel sites)).wp P
  have hx := fun family addr packets mtu => (wgXmit_cell family addr packets mtu).wp P
  have hd (α : Type) := discard_view_spec cell (α := α) P
  mvcgen [Leanux.Env.Stack.reply4, hc, hx, hd, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals rfl

theorem receive4_cell (bytes : List UInt8) :
    SameView cell (Leanux.Env.Stack.receive4 bytes) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hr := fun dst bytes => (reply4_cell dst bytes).wp P
  mvcgen [Leanux.Env.Stack.receive4, Leanux.Env.Stack.excluded, hr, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals rfl

theorem deliverInner_cell (bytes : List UInt8) : SameView cell (Leanux.Env.deliverInner bytes) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have h4 := (receive4_cell bytes).wp P
  have h6 := (cell_kernel (stackReceive6_sameKernel bytes)).wp P
  mvcgen [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, h4, h6, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals rfl

theorem stackForM_cell (packets : List (List UInt8)) :
    SameView cell (packets.forM Leanux.Env.deliverInner) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (cell w)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (cell w)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := (deliverInner_cell bytes).wp P
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  all_goals try subst s
  all_goals rfl

end Leanux.Proofs.WG.Queues.RxRing
