import Leanux.Proofs.WG.Origins.RetainingLeaves
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.RxTxFrames
import Leanux.Proofs.WG.Queues.TxDispositionEndpoints
import Leanux.Proofs.WG.Queues.TxRingWorker
import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.RxRingWorker
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.WG.Lifetimes.BatchNapi
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.Framing.WGReceiveHeaders

/-! Original non-installing packet paths retain every surviving valid receiving
material and its nullable owner. Callback contracts are explicit until discharged
by the actual stack; neither residence nor packet authorization is asserted. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Std.Do
set_option pp.structureInstances false

theorem getTxSkb_material (id : SkbId) : SameView view (getTxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb, getDev, getK, invariant]

theorem setTxSkb_material (id : SkbId) (f : DataPacket → DataPacket) :
    SameView view (setTxSkb id f) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_material id).wp (fun t => t = s)
  have hm := fun p => (modifyDev_material (fun d => {d with txSkbs := d.txSkbs.insert id (f p)})
    (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [setTxSkb, hg, hm]

theorem newTxSkb_material (p : DataPacket) : SameView view (newTxSkb p) := by
  apply SameView.of_wp
  intro s
  mvcgen [newTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState]

theorem freeTxSkb_material (id : SkbId) : SameView view (freeTxSkb id) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_material id).wp (fun t => t = s)
  have hm := (modifyDev_material (fun d => {d with txSkbs := d.txSkbs.erase id}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [freeTxSkb, hg, hm]

theorem sendQueuedHandshakeInitiation_material (pid : PeerId) (retry : Bool) :
    RetainsCall (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hn := (requireNotPending_material pid "queueing a handshake").wp P
  have hc := fun date => (kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))).wp P
  have hget := (peerGet_material pid).wp P
  have hput := (peerPut_material (some pid)).wp P
  have hrec := (kernel (recordQueued_sameKernel .sendWorker pid)).wp P
  have hqueue := (modifyDev_material (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl)).wp P
  mvcgen [sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hrec, hqueue, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all [materialState])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsView.refl _

theorem txDevice_material (u : TxDeviceUpdate) : SameView view (modifyDev u.apply) :=
  modifyDev_material _ (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_material (pid : PeerId) : SameView view (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch]
  all_goals try exact ((⇓? _ w => ⌜view w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_material (pid : PeerId) (item : List SkbId) :
    SameView view (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hp := fun id f => (setTxSkb_material id f).wp (fun t => t = s)
  have hc := fun last => (kernel (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (kernel (queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t = s)
  have hd := fun u => (txDevice_material u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hp, hc, hw, hcpu, hring, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem enqueuePerPeerTx_material (item : List SkbId) (state : PacketState) :
    RetainsCall (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have htx := fun id => (getTxSkb_material id).wp P
  have hk := fun id => (getKeypair_material id).wp P
  have hg := fun pid => (getPeer_material pid).wp P
  have hget := fun pid => (peerGet_material pid).wp P
  have hput := fun pid => (peerPut_material pid).wp P
  have hset := fun id f => (setTxSkb_material id f).wp P
  have hcpu := fun pid => (cpumaskChooseOnline_material pid).wp P
  have hpeek := fun pid => (kernel (peekQueuedUnit_sameKernel .txWorker pid)).wp P
  have hrec := fun pid => (kernel (recordQueued_sameKernel .txWorker pid)).wp P
  have hdev := fun pid => (txDevice_material (.work pid)).wp P
  have hw := fun o => (ownerDeref_material o).wp P
  mvcgen [hw, enqueuePerPeerTx, htx, hk, hg, hget, hput, hset, hcpu, hpeek, hrec, hdev,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsView.refl _

theorem createData_material (pid : PeerId) (item : List SkbId) : RetainsCall (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := (getPeer_material pid).wp P
  have ht := fun id => (getTxSkb_material id).wp P
  have hd := (enqueuePerDeviceAndPeer_material pid item).wp P
  have hp := (enqueuePerPeerTx_material item .dead).wp s
  have hk := fun id => (keypairPut_material id false).wp s
  have hr := (peerPut_material (some pid)).wp P
  have hf := fun id => (freeTxSkb_material id).wp P
  mvcgen [createData, hg, ht, hd, hp, hk, hr, hf, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | trivial | simp_all [KeyLe,MaterialOrigin.material,WordLe]

theorem stagedOutNokey_material (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsCall (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply ProjectedAction.of_wp <;> intro s
  all_goals
    let P := RetainsView s
    have hg := material_getPeer P pid
    have hs := fun p => material_setPeer P pid p
    have hk := getKeypair_spec P
    have hset := setKeypair_spec P (fun _ _ hr hi => hi.trans hr)
    have hp := fun kp => (keypairPut_material kp false).wp s
    have hq := (sendQueuedHandshakeInitiation_material pid false).wp s
    have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | trivial | simp_all [KeyLe,MaterialOrigin.material,WordLe]

theorem newTxSkbs_material (packets : List DataPacket) : SameView view (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact SameView.bind (newTxSkb_material p) (fun _ => SameView.bind ih (fun _ => SameView.pure _ _))

theorem sendStagedPackets_material (pid : PeerId) : RetainsCall (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hk := getKeypair_spec P
  have hset := setKeypair_spec P (fun _ _ hr hi => hi.trans hr)
  have hget := fun kp => (keypairGet_material kp).wp s
  have hp := fun pid => (peerGet_material pid).wp P
  have hout := fun packets kp invalid => (stagedOutNokey_material pid packets kp invalid).wp s
  have hput := fun kp => (keypairPut_material kp false).wp s
  have hqueue := (sendQueuedHandshakeInitiation_material pid false).wp s
  have ht := fun date => (kernel (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME)).wp P
  have he := fun pkt => (kernel (ipTunnelEcnEncap_sameKernel pkt)).wp P
  have hn := fun packets => (newTxSkbs_material packets).wp P
  have hc := fun item => (createData_material pid item).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => (kernel (indexOwner_peerDeref_sameKernel o)).wp P
  mvcgen [hw,-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | trivial | simp_all [KeyLe,MaterialOrigin.material,WordLe]


theorem sendKeepalive_material (pid : PeerId) : RetainsCall (sendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have ha := (kernel (hiddenAlloc_sameKernel .keepaliveSkb)).wp P
  have ht := (sendStagedPackets_material pid).wp s
  mvcgen [sendKeepalive, hg, hs, ha, ht, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all [materialState])
  all_goals try assumption
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsView.refl _

private theorem borrowed_material (hb : PeerBorrow.Borrowed w.k result v.k) :
    view v = view w := by
  cases result with
  | none => change v.k = w.k at hb; simp [view, hb]
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    simp [view, hk, hd]

theorem lookup_material (root : Option NodeId) (bits key : Nat) :
    SameView view (lookup root bits key) := by
  intro w result v hr
  exact borrowed_material ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookup_spec root bits key w.k) w result v rfl hr)

theorem lookupSrc_material (protocol : Nat) (bytes : List UInt8) :
    SameView view (lookupSrc protocol bytes) := by
  intro w result v hr
  exact borrowed_material ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookupSrc_spec protocol bytes w.k) w result v rfl hr)

theorem lookupDst_material (family addr : Nat) : SameView view (lookupDst family addr) := by
  intro w result v hr
  exact borrowed_material ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookupDst_spec family addr w.k) w result v rfl hr)

theorem sendSkbToPeer_material (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView view (sendSkbToPeer pid bytes ds) := by
  apply SameView.of_wp
  intro s
  have hp := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have h4 := fun e => (send4_material e (some pid) bytes ds true).wp (fun t => t = s)
  have h6 := fun e => (send6_material e (some pid) bytes ds true).wp (fun t => t = s)
  mvcgen [sendSkbToPeer, hp, hs, h4, h6, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState]

theorem timersDataSent_material (pid : PeerId) : SameView view (timersDataSent pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_material pid).wp (fun t => t = s)
  have hj := (kernel (jitterBelowRekeyTimeout_sameKernel .newHandshakeJitter)).wp (fun t => t = s)
  have hg := (modPeerTimerGuard_material pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_material pid .newHandshake n jc).wp (fun t => t = s)
  have hc := (kernel (callerJiffies_sameKernel .timerJiffiesDataSent)).wp (fun t => t = s)
  mvcgen [timersDataSent, hp, hj, hg, ha, hc, branch]

theorem keepKeyFresh_material (pid : PeerId) : RetainsCall (keepKeyFresh pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hp := (getPeer_material pid).wp P
  have hk := fun id => (getKeypair_material id).wp P
  have he := fun d birth age => (kernel (branchExpired_sameKernel d birth age)).wp P
  have hh := (sendQueuedHandshakeInitiation_material pid false).wp s
  mvcgen [keepKeyFresh, hp, hk, he, hh, WG.andM, WG.orM, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem createDataDone_material (pid : PeerId) (item : List SkbId) :
    RetainsCall (createDataDone pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have ht := (timersTraversal_material pid).wp P
  have ha := (timersAnyAuthenticatedPacketSent_material pid).wp P
  have hg := fun id => (getTxSkb_material id).wp P
  have hs := fun bytes ds => (sendSkbToPeer_material pid bytes ds).wp P
  have hd := (timersDataSent_material pid).wp P
  have hk := (keepKeyFresh_material pid).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    createDataDone, ht, ha, hg, hs, hd, hk, WG.andM, branch]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem txStep_material (pid : PeerId) : RetainsCall (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hp := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hg := fun id => (getTxSkb_material id).wp P
  have hq := fun (q : PrevQueue (List SkbId)) => (kernel (prevQueuePeek_sameKernel q)).wp P
  have hd := fun item => (createDataDone_material pid item).wp s
  have hf := fun id => (freeTxSkb_material id).wp P
  have hk := fun kp => (keypairPut_material kp false).wp s
  have hu := (peerPut_material (some pid)).wp P
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  simp only [TxDisposition.stepSource, TxDisposition.bodySource, TxDisposition.disposeSource, getPeer_twice]
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hs, hg, hq, hd, hf, hk, hu, WG.andM, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem workerIter_material (worker : Worker) (pid : Option Nat) (step afterItem : M Bool)
    (hs : RetainsCall step) (ha : RetainsCall afterItem) :
    RetainsCall (workerIter worker pid step afterItem) := by
  apply ProjectedAction.of_wp
  intro s
  have hstep := hs.wp s
  have hafter := ha.wp s
  mvcgen [workerIter, hstep, hafter]
  subst s
  exact RetainsView.refl _

theorem txIter_material (pid : PeerId) (need : M Bool) (hn : RetainsCall need) :
    RetainsCall (txIter pid need) := by
  apply workerIter_material _ _ _ _ (txStep_material pid)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsView.refl _

theorem xmitTrim_material (pid : PeerId) : SameView view (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_material (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch]
  all_goals try exact ((⇓? _ w => ⌜view w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [view, materialState]

theorem xmitSplice_material (pid : PeerId) (packets : List Packet) :
    SameView view (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_material pid (fun p => {p with staged := p.staged ++ packets})

/-- Original transmit entry retains receiving material on every normal
return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_material (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsCall (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := fun pid => (getPeer_material pid).wp P
  have hlookup := (lookupDst_material family addr).wp P
  have htrim := fun pid => (xmitTrim_material pid).wp P
  have hsplice := fun pid packets => (xmitSplice_material pid packets).wp P
  have hstage := fun pid => (sendStagedPackets_material pid).wp s
  have hput := fun pid => (peerPut_material pid).wp P
  have hloop := fun sites raised => (kernel (loopbackSend_kernel sites raised)).wp P
  have hcut := fun sites => (kernel (skipCutSites_sameKernel sites)).wp P
  have henv := fun site => (kernel (envOk_sameKernel site)).wp P
  have herr := (modifyDev_material (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, wgXmitSource,
    hg, hlookup, htrim, hsplice, hstage, hput, hloop, hcut, henv, herr,
    WG.andM, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | trivial

theorem reply4_material (dst : Nat) (bytes : List UInt8) :
    RetainsCall (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hc := fun sites => (kernel (skipCut_sameKernel sites)).wp P
  have hx := fun family addr packets mtu => (wgXmit_material family addr packets mtu).wp s
  have hd (α : Type) := discard_view_spec view (α := α) P
  mvcgen [Leanux.Env.Stack.reply4, hc, hx, hd, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem receive4_material (bytes : List UInt8) :
    RetainsCall (Leanux.Env.Stack.receive4 bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hr := fun dst bytes => (reply4_material dst bytes).wp s
  mvcgen [Leanux.Env.Stack.receive4, Leanux.Env.Stack.excluded, hr, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem deliverInner_material (bytes : List UInt8) : RetainsCall (Leanux.Env.deliverInner bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have h4 := (receive4_material bytes).wp s
  have h6 := (kernel (stackReceive6_sameKernel bytes)).wp P
  mvcgen [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, h4, h6, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem stackForM_material (packets : List (List UInt8)) :
    RetainsCall (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (view w)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := (deliverInner_material bytes).wp s
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  subst s
  exact RetainsView.refl _


theorem encryptPacket_material (checksum : Packet → M Packet)
    (hc : ∀ p, RetainsCall (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    RetainsCall (encryptPacket checksum key pkt) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hcut := (kernel (skipCut_sameKernel [.flowHashSecret])).wp P
  have hpad := (kernel (calculateSkbPadding_sameKernel pkt.plaintext.bytes.length pkt.plaintext.mtu)).wp P
  have halloc := fun site => (kernel (hiddenAlloc_sameKernel site)).wp P
  have hchecksum := fun p => (hc p).wp s
  have hkey := (getKeypair_material key).wp P
  mvcgen [encryptPacket, hcut, hpad, halloc, hchecksum, hkey, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

private theorem encryptPoll_material : SameView view TxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have hm := fun ring => (modifyDev_material (fun d => {d with encryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [TxRing.pollSource, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem encryptStep_material (checksum : Packet → M Packet) (softirq : M Unit)
    (hc : ∀ p, RetainsCall (checksum p)) (hi : RetainsCall softirq) :
    RetainsCall (encryptStep checksum softirq) := by
  rw [← TxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hir := hi.wp s
  have hp := encryptPoll_material.wp P
  have hg := fun id => (getTxSkb_material id).wp P
  have he := fun key pkt => (encryptPacket_material checksum hc key pkt).wp s
  have hs := fun id f => (setTxSkb_material id f).wp P
  have hq := fun first state => (enqueuePerPeerTx_material first state).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    TxRing.stepSource, hir, hp, hg, he, hs, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem encryptIter_material (checksum : Packet → M Packet) (softirq : M Unit) (need : M Bool)
    (hc : ∀ p, RetainsCall (checksum p)) (hi : RetainsCall softirq)
    (hn : RetainsCall need) : RetainsCall (encryptIter checksum softirq need) := by
  apply workerIter_material _ _ _ _ (encryptStep_material checksum softirq hc hi)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsView.refl _

theorem actualChecksum_material (pkt : Packet) : RetainsCall (Leanux.Env.checksumHelp pkt) :=
  .of_same (kernel (checksumHelp_sameKernel pkt))
theorem getRxSkb_material (id : SkbId) : SameView view (getRxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getRxSkb, getDev, getK, invariant]

theorem setRxSkb_material (id : SkbId) (f : RxPacket → RxPacket) :
    SameView view (setRxSkb id f) := by
  unfold setRxSkb
  exact (getRxSkb_material id).bind fun _ => modifyDev_material _ (fun _ => rfl)

theorem freeRxSkb_material (id : SkbId) : SameView view (freeRxSkb id) := by
  unfold freeRxSkb
  exact (getRxSkb_material id).bind fun _ => modifyDev_material _ (fun _ => rfl)

theorem decryptPacket_material (pkt : RxPacket) : RetainsCall (decryptPacket pkt) := by
  intro w x v hr
  exact (hoare_iff_triple _ _ _).mpr
    (decrypt_spec (RetainsView (view w)) (fun _ _ hr hi => hi.trans hr) pkt)
    w x v (RetainsView.refl _) hr

theorem counterValidate_material (kp : KeypairId) (nonce : Nat) :
    RetainsCall (counterValidate kp nonce) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := getKeypair_spec (fun t => t = s) kp
  have hs := setKeypair_spec (RetainsView s) (fun _ _ hr hi => hi.trans hr) kp
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,
    counterValidate,hg,hs,branch,branchCmp,WG.orM,invariant]
  all_goals try exact ((⇓? _ w => ⌜view w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try mvcgen_trivial
  all_goals try simp_all [view,KeyLe,MaterialOrigin.material,WordLe,RetainsView.refl]
  all_goals try subst s
  all_goals
    intro hv
    refine ⟨_, ?_, hv, ⟨rfl, rfl, rfl⟩, Or.inr rfl⟩
    grind only

theorem receivedWithKeypair_material (pid : PeerId) (kp : KeypairId) :
    RetainsCall (receivedWithKeypair pid kp) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := (getPeer_view pid).wp P
  have hk := fun old => (keypairPut_material old true).wp s
  have hm := modifyPeer_spec P pid
  mvcgen [receivedWithKeypair,hg,hk,hm,branch,invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem timersHandshakeComplete_material (pid : PeerId) (site : HiddenSite) :
    SameView view (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hd := (delTimer_material pid .retransmitHandshake).wp (fun t => t = s)
  have hh := (kernel (hidden_sameKernel site)).wp (fun t => t = s)
  mvcgen [timersHandshakeComplete, hg, hs, hd, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState]

theorem timersAnyAuthenticatedPacketReceived_material (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketReceived pid) := delTimer_material pid .newHandshake

theorem timersDataReceived_material (pid : PeerId) : SameView view (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have ht := (modPeerTimer_material .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec view (fun t => t = s) _ ht
  mvcgen [timersDataReceived, hg, hs, ht, hd, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState]

theorem keepKeyFreshRx_material (pid : PeerId) : RetainsCall (keepKeyFreshRx pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hg := material_getPeer P pid
  have hs := fun p => material_setPeer P pid p
  have hk := fun id => (getKeypair_material id).wp P
  have ht := fun date delay => (kernel (branchExpired_sameKernel .rxFreshExpired date delay)).wp P
  have hq := (sendQueuedHandshakeInitiation_material pid false).wp s
  mvcgen [keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem dishonest_material (why : Dishonest) : SameView view (dishonest why) :=
  modifyDev_material _ (fun d => by cases why <;> rfl)

theorem updateRxStats_material (pid : PeerId) (len : Nat) :
    SameView view (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_material (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold view at *; simp_all [materialState]

theorem consumeDataDone_material (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsCall (consumeDataDone pid pkt endpoint) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hep := (setPeerEndpoint_material pid endpoint).wp P
  have hk := (receivedWithKeypair_material pid pkt.keypair).wp s
  have hh := (timersHandshakeComplete_material pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_material pid).wp s
  have hf := (keepKeyFreshRx_material pid).wp s
  have ha := (timersAnyAuthenticatedPacketReceived_material pid).wp P
  have htr := (timersTraversal_material pid).wp P
  have hdata := (timersDataReceived_material pid).wp P
  have hstats := fun len => (updateRxStats_material pid len).wp P
  have herr := fun why => (dishonest_material why).wp P
  have hecn := fun protocol outer bytes => (kernel (inetEcnDecapsulate_sameKernel protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_material protocol bytes).wp P
  have hp := fun peer => (peerPut_material peer).wp P
  mvcgen [consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all)
  all_goals subst s
  all_goals exact RetainsView.refl _

private theorem peekRxQueue_material (pid : PeerId) : SameView view (peekRxQueue pid) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t => t = s) pid
  have hs := fun p => material_setPeer (fun t => t = s) pid p
  have hq := fun (q : PrevQueue SkbId) => (kernel (prevQueuePeek_sameKernel q)).wp (fun t => t = s)
  mvcgen [peekRxQueue, hg, hs, hq]
  all_goals simp_all

private theorem dropRxQueue_material (pid : PeerId) : SameView view (dropRxQueue pid) := by
  simp only [dropRxQueue, getPeer_twice]
  exact modifyPeer_material pid _

private theorem completeRxQueue_material (pid : PeerId) : SameView view (completeRxQueue pid) :=
  modifyPeer_material pid _

theorem groNormalList_material (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsCall (cb xs)) (g : GroState) : RetainsCall (groNormalList cb g) := by
  apply ProjectedAction.of_wp
  intro s
  have hcb := fun xs => (hc xs).wp s
  mvcgen [groNormalList, hcb]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem groNormalOne_material (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsCall (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    RetainsCall (groNormalOne cb g pkt segs) := by
  apply ProjectedAction.of_wp
  intro s
  have hl := fun g => (groNormalList_material cb hc g).wp s
  mvcgen [groNormalOne, hl]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem napiGroReceive_material (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsCall (cb xs)) (g : GroState) (pkt : List UInt8) :
    RetainsCall (napiGroReceive cb g pkt) := by
  apply ProjectedAction.of_wp
  intro s
  have hn := fun g pkt segs => (groNormalOne_material cb hc g pkt segs).wp s
  mvcgen [napiGroReceive, hn, unsupported]
  all_goals subst s
  all_goals exact RetainsView.refl _

theorem napiGroFlushAll_material (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsCall (cb xs)) (g : GroState) :
    RetainsCall (napiGroFlushAll cb g) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hn := fun g pkt segs => (groNormalOne_material cb hc g pkt segs).wp s
  have hl := fun g => (groNormalList_material cb hc g).wp s
  have hlist (α β : Type) := list_view_spec view (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hlist, napiGroFlushAll, hn, hl]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem rxPoll_material (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsCall (cb xs)) : RetainsCall (rxPoll pid budget cb) := by
  rw [← rxPollGrouped_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hp := (peekRxQueue_material pid).wp P
  have hdrop := (dropRxQueue_material pid).wp P
  have hcomplete := (completeRxQueue_material pid).wp P
  have hr := fun id => (getRxSkb_material id).wp P
  have hctr := fun key nonce => (counterValidate_material key nonce).wp s
  have he := fun src => (kernel (endpointFromSkb_sameKernel src)).wp P
  have hd := fun pkt ep => (consumeDataDone_material pid pkt ep).wp s
  have hg := fun g pkt => (napiGroReceive_material cb hc g pkt).wp s
  have hf := fun g => (napiGroFlushAll_material cb hc g).wp s
  have hk := fun kp => (keypairPut_material kp false).wp s
  have hu := (peerPut_material (some pid)).wp P
  have hx := fun id => (freeRxSkb_material id).wp P
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) P
  simp only [rxPollGrouped, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hdrop, hcomplete, hr, hctr, he, hd, hg, hf, hk, hu, hx, WG.andM, branch, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem actualRxPoll_material (pid : PeerId) (budget : Nat) :
    RetainsCall (rxPoll pid budget (fun xs => xs.forM Leanux.Env.deliverInner)) :=
  rxPoll_material pid budget _ stackForM_material

theorem enqueuePerPeerRx_material (irq : M Unit) (hi : RetainsCall irq)
    (id : SkbId) (state : PacketState) : RetainsCall (enqueuePerPeerRx irq id state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hk := fun id => (getKeypair_material id).wp P
  have hget := fun pid => (peerGet_material pid).wp P
  have hp := fun pid => material_getPeer P pid
  have hs := fun pid p => material_setPeer P pid p
  have hir := hi.wp s
  have hput := fun pid => (peerPut_material pid).wp P
  have hw := fun o => (ownerDeref_material o).wp P
  mvcgen [hw, enqueuePerPeerRx, hk, hget, hp, hs, hir, hput,
    setRxSkb, getRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [view, materialState, Option.bind_map, Function.comp_def]
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

private theorem decryptPoll_material : SameView view RxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have hm := fun ring => (modifyDev_material (fun d => {d with decryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [RxRing.pollSource, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem decryptStep_material (softirq irq : M Unit)
    (hs : RetainsCall softirq) (hi : RetainsCall irq) :
    RetainsCall (decryptStep softirq irq) := by
  rw [← RxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hsoft := hs.wp s
  have hp := decryptPoll_material.wp P
  have hg := fun id => (getRxSkb_material id).wp P
  have hd := fun pkt => (decryptPacket_material pkt).wp s
  have hset := fun id f => (setRxSkb_material id f).wp P
  have hq := fun id state => (enqueuePerPeerRx_material irq hi id state).wp s
  mvcgen [RxRing.stepSource, hsoft, hp, hg, hd, hset, hq, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem decryptIter_material (softirq irq : M Unit) (need : M Bool)
    (hs : RetainsCall softirq) (hi : RetainsCall irq) (hn : RetainsCall need) :
    RetainsCall (decryptIter softirq irq need) := by
  apply workerIter_material _ _ _ _ (decryptStep_material softirq irq hs hi)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsView.refl _
theorem newRxSkb_material (pkt : RxPacket) : SameView view (newRxSkb pkt) := by
  apply SameView.of_wp
  intro s
  mvcgen [newRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem enqueuePerDeviceAndPeerRx_material (id : SkbId) :
    SameView view (enqueuePerDeviceAndPeerRx id) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => material_getPeer (fun t => t = s) pid
  have hset := fun pid p => material_setPeer (fun t => t = s) pid p
  have hr := (getRxSkb_material id).wp (fun t => t = s)
  have hs := fun f => (setRxSkb_material id f).wp (fun t => t = s)
  have hc := fun last => (kernel (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (kernel (queueDeviceWork_sameKernel .decryptWorker)).wp (fun t => t = s)
  mvcgen [enqueuePerDeviceAndPeerRx, hp, hset, hr, hs, hc, hw,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold view at *; simp_all [materialState, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem consumeData_material (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    RetainsCall (consumeData msg src ds) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hl := (indexLookup_retains [.keypair] (u32le msg 4)).wp P (fun _ _ hr hi => hi.trans hr)
  have hg := fun kp => (keypairGet_material kp).wp s
  have hp := fun pid => (getPeer_material pid).wp P
  have hn := fun pkt => (newRxSkb_material pkt).wp P
  have he := fun id => (enqueuePerDeviceAndPeerRx_material id).wp P
  have hq := fun id => (enqueuePerPeerRx_material (pure ())
    (.of_same (SameView.pure view ())) id .dead).wp s
  have hk := fun kp => (keypairPut_material kp false).wp s
  have hu := fun pid => (peerPut_material pid).wp P
  have hf := fun id => (freeRxSkb_material id).wp P
  mvcgen [consumeData, hl, hg, hp, hn, he, hq, hk, hu, hf,
    keypairGetCurrent, WG.orM, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem cpumaskNextOnline_material : SameView view cpumaskNextOnline := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskNextOnline, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [view, materialState, Option.map_map, Function.comp_def]
  all_goals assumption

theorem packetReceive_material (msg : List UInt8) (src : SkbSource) :
    RetainsCall (packetReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsView s
  have hh := (kernel (prepareSkbHeader_sameKernel msg)).wp P
  have hd := fun protocol bytes => (kernel (ipTunnelGetDsfield_sameKernel protocol bytes)).wp P
  have hc := fun ds => (consumeData_material msg src ds).wp s
  have hn := cpumaskNextOnline_material.wp P
  have hw := (kernel (queueDeviceWork_sameKernel .receiveWorker)).wp P
  have hm := (modifyDev_material (fun d => {d with handshakeQueue := d.handshakeQueue.produce (msg, src), handshakeQueueLen := d.handshakeQueueLen + 1}) (fun _ => rfl)).wp P
  mvcgen [packetReceive, hh, hd, hc, hn, hw, hm, getDev, getK, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem wgReceive_material (msg : List UInt8) (src : SkbSource) :
    RetainsCall (wgReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := (packetReceive_material msg src).wp s
  mvcgen [wgReceive, hp, branch, unsupported]
  all_goals subst s
  all_goals exact RetainsView.refl _
theorem runWorker_material (worker : Worker) (body : M Unit)
    (hb : RetainsCall body) : RetainsCall (Env.runWorker worker body) := by
  apply ProjectedAction.of_wp
  intro s
  have hbody := hb.wp s
  have hh := fun site => (kernel (hidden_sameKernel site)).wp (RetainsView s)
  mvcgen [Env.runWorker, hbody, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

private theorem pendingPolls_material (pending : List PeerId) :
    RetainsCall (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := fun pid => (actualRxPoll_material pid NAPI_POLL_WEIGHT).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (RetainsView s)
  have hd (α : Type) := discard_view_spec view (α := α) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd, hp]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem napiSoftirq_material : RetainsCall Env.napiSoftirq := by
  apply ProjectedAction.of_wp
  intro s
  have hw := fun pending => (runWorker_material .netRx _ (pendingPolls_material pending)).wp s
  have hh := (kernel peekHiddenSite_sameKernel).wp (RetainsView s)
  mvcgen [Env.napiSoftirq, hw, hh, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

/-- The second actual direct poll site runs without opening a new section. -/
theorem pollScheduledInline_material : RetainsCall Env.pollScheduledInline := by
  apply ProjectedAction.of_wp
  intro s
  have hp := fun pid => (actualRxPoll_material pid NAPI_POLL_WEIGHT).wp s
  have hl (α β : Type) := list_view_spec view (α := α) (β := β) (RetainsView s)
  have hd (α : Type) := discard_view_spec view (α := α) (RetainsView s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd,
    Env.pollScheduledInline, hp, getDev, getK, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsView s (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem napiIrqExit_material : RetainsCall Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  have hn := napiSoftirq_material.wp s
  have hc := (kernel chooseNapiHere_sameKernel).wp (RetainsView s)
  have hh := (kernel peekHiddenSite_sameKernel).wp (RetainsView s)
  mvcgen [napiIrqExitSource, hn, hc, hh, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold view at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsView.refl _ | assumption

theorem actualEncryptStep_material : RetainsCall (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_material _ _ actualChecksum_material napiSoftirq_material

theorem actualEncryptIter_material :
    RetainsCall (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  encryptIter_material _ _ _ actualChecksum_material napiSoftirq_material
    (.of_same (kernel (Framing.condResched_sameKernel .encryptWorker)))

theorem actualDecryptStep_material : RetainsCall (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_material _ _ napiSoftirq_material napiIrqExit_material

theorem actualDecryptIter_material :
    RetainsCall (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  decryptIter_material _ _ _ napiSoftirq_material napiIrqExit_material
    (.of_same (kernel (Framing.condResched_sameKernel .decryptWorker)))

theorem actualTxIter_material (pid : PeerId) : RetainsCall (txIter pid (Env.condResched .txWorker)) :=
  txIter_material _ _ (.of_same (kernel (Framing.condResched_sameKernel .txWorker)))

end Leanux.Proofs.WG.Origins.Retaining
