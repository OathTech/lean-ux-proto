import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.TxDispositionEndpoints
import Leanux.Proofs.WG.Queues.TxRingWorker
import Leanux.Proofs.Framing.WGData

/-! Original TX and stack calls preserve routing tables, allocation frontiers
and every surviving resident list. Peer releases may delete residents. These
are normal-endpoint frames, not packet authorization or termination claims. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

private theorem borrowed_routing (hb : PeerBorrow.Borrowed w.k result v.k) :
    routingView v = routingView w := by
  cases result with
  | none => change v.k = w.k at hb; simp [routingView, hb]
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    simp [routingView, hk, hd, hs]

theorem lookup_routing (root : Option NodeId) (bits key : Nat) :
    SameView routingView (lookup root bits key) := by
  intro w result v hr
  exact borrowed_routing ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookup_spec root bits key w.k) w result v rfl hr)

theorem lookupSrc_routing (protocol : Nat) (bytes : List UInt8) :
    SameView routingView (lookupSrc protocol bytes) := by
  intro w result v hr
  exact borrowed_routing ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookupSrc_spec protocol bytes w.k) w result v rfl hr)

theorem lookupDst_routing (family addr : Nat) : SameView routingView (lookupDst family addr) := by
  intro w result v hr
  exact borrowed_routing ((hoare_iff_triple _ _ _).mpr
    (RxBorrow.lookupDst_spec family addr w.k) w result v rfl hr)

theorem sendSkbToPeer_routing (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView routingView (sendSkbToPeer pid bytes ds) := by
  apply SameView.of_wp
  intro s
  have hp := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have h4 := fun e => (send4_routing e (some pid) bytes ds true).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e (some pid) bytes ds true).wp (fun t => t = s)
  mvcgen [sendSkbToPeer, hp, hs, h4, h6, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem timersDataSent_routing (pid : PeerId) : SameView routingView (timersDataSent pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_routing pid).wp (fun t => t = s)
  have hj := (routing_kernel _ (jitterBelowRekeyTimeout_sameKernel .newHandshakeJitter)).wp (fun t => t = s)
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_routing pid .newHandshake n jc).wp (fun t => t = s)
  have hc := (routing_kernel _ (callerJiffies_sameKernel .timerJiffiesDataSent)).wp (fun t => t = s)
  mvcgen [timersDataSent, hp, hj, hg, ha, hc, branch]

theorem keepKeyFresh_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFresh pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := (getPeer_routing pid).wp P
  have hk := fun id => (getKeypair_routing id).wp P
  have he := fun d birth age => (routing_kernel _ (branchExpired_sameKernel d birth age)).wp P
  have hh := (sendQueuedHandshakeInitiation_routing pid false).wp s
  mvcgen [keepKeyFresh, hp, hk, he, hh, WG.andM, WG.orM, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem createDataDone_routing (pid : PeerId) (item : List SkbId) :
    RetainsRoutingCall (createDataDone pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ht := (timersTraversal_routing pid).wp P
  have ha := (timersAnyAuthenticatedPacketSent_routing pid).wp P
  have hg := fun id => (getTxSkb_routing id).wp P
  have hs := fun bytes ds => (sendSkbToPeer_routing pid bytes ds).wp P
  have hd := (timersDataSent_routing pid).wp P
  have hk := (keepKeyFresh_routing pid).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    createDataDone, ht, ha, hg, hs, hd, hk, WG.andM, branch]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem txStep_routing (pid : PeerId) : RetainsRoutingCall (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hg := fun id => (getTxSkb_routing id).wp P
  have hq := fun (q : PrevQueue (List SkbId)) => (routing_kernel _ (prevQueuePeek_sameKernel q)).wp P
  have hd := fun item => (createDataDone_routing pid item).wp s
  have hf := fun id => (freeTxSkb_routing id).wp P
  have hk := fun kp => (keypairPut_routing kp false).wp P
  have hu := (peerPut_retainsRouting (some pid)).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  simp only [TxDisposition.stepSource, TxDisposition.bodySource, TxDisposition.disposeSource, getPeer_twice]
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hs, hg, hq, hd, hf, hk, hu, WG.andM, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem workerIter_routing (worker : Worker) (pid : Option Nat) (step afterItem : M Bool)
    (hs : RetainsRoutingCall step) (ha : RetainsRoutingCall afterItem) :
    RetainsRoutingCall (workerIter worker pid step afterItem) := by
  apply ProjectedAction.of_wp
  intro s
  have hstep := hs.wp s
  have hafter := ha.wp s
  mvcgen [workerIter, hstep, hafter]
  subst s
  exact RetainsRouting.refl _

theorem txIter_routing (pid : PeerId) (need : M Bool) (hn : RetainsRoutingCall need) :
    RetainsRoutingCall (txIter pid need) := by
  apply workerIter_routing _ _ _ _ (txStep_routing pid)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsRouting.refl _

theorem xmitTrim_routing (pid : PeerId) : SameView routingView (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_routing (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]

theorem xmitSplice_routing (pid : PeerId) (packets : List Packet) :
    SameView routingView (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_routing pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl)

/-- Original transmit entry retains routing data and surviving lists on every normal
return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_routing (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsRoutingCall (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := fun pid => (getPeer_routing pid).wp P
  have hlookup := (lookupDst_routing family addr).wp P
  have htrim := fun pid => (xmitTrim_routing pid).wp P
  have hsplice := fun pid packets => (xmitSplice_routing pid packets).wp P
  have hstage := fun pid => (sendStagedPackets_routing pid).wp s
  have hput := fun pid => (peerPut_retainsRouting pid).wp s
  have hloop := fun sites raised => (routing_kernel _ (loopbackSend_kernel sites raised)).wp P
  have hcut := fun sites => (routing_kernel _ (skipCutSites_sameKernel sites)).wp P
  have henv := fun site => (routing_kernel _ (envOk_sameKernel site)).wp P
  have herr := (modifyDev_routing (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, wgXmitSource,
    hg, hlookup, htrim, hsplice, hstage, hput, hloop, hcut, henv, herr,
    WG.andM, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem reply4_routing (dst : Nat) (bytes : List UInt8) :
    RetainsRoutingCall (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hc := fun sites => (routing_kernel _ (skipCut_sameKernel sites)).wp P
  have hx := fun family addr packets mtu => (wgXmit_routing family addr packets mtu).wp s
  have hd (α : Type) := discard_view_spec routingView (α := α) P
  mvcgen [Leanux.Env.Stack.reply4, hc, hx, hd, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem receive4_routing (bytes : List UInt8) :
    RetainsRoutingCall (Leanux.Env.Stack.receive4 bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hr := fun dst bytes => (reply4_routing dst bytes).wp s
  mvcgen [Leanux.Env.Stack.receive4, Leanux.Env.Stack.excluded, hr, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem deliverInner_routing (bytes : List UInt8) : RetainsRoutingCall (Leanux.Env.deliverInner bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have h4 := (receive4_routing bytes).wp s
  have h6 := (routing_kernel _ (stackReceive6_sameKernel bytes)).wp P
  mvcgen [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, h4, h6, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem stackForM_routing (packets : List (List UInt8)) :
    RetainsRoutingCall (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (routingView w)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (routingView w)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := (deliverInner_routing bytes).wp s
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  subst s
  exact RetainsRouting.refl _


theorem encryptPacket_routing (checksum : Packet → M Packet)
    (hc : ∀ p, RetainsRoutingCall (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    RetainsRoutingCall (encryptPacket checksum key pkt) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hcut := (routing_kernel _ (skipCut_sameKernel [.flowHashSecret])).wp P
  have hpad := (routing_kernel _ (calculateSkbPadding_sameKernel pkt.plaintext.bytes.length pkt.plaintext.mtu)).wp P
  have halloc := fun site => (routing_kernel _ (hiddenAlloc_sameKernel site)).wp P
  have hchecksum := fun p => (hc p).wp s
  have hkey := (getKeypair_routing key).wp P
  mvcgen [encryptPacket, hcut, hpad, halloc, hchecksum, hkey, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem encryptPoll_routing : SameView routingView TxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have hm := fun ring => (modifyDev_routing (fun d => {d with encryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [TxRing.pollSource, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem encryptStep_routing (checksum : Packet → M Packet) (softirq : M Unit)
    (hc : ∀ p, RetainsRoutingCall (checksum p)) (hi : RetainsRoutingCall softirq) :
    RetainsRoutingCall (encryptStep checksum softirq) := by
  rw [← TxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hir := hi.wp s
  have hp := encryptPoll_routing.wp P
  have hg := fun id => (getTxSkb_routing id).wp P
  have he := fun key pkt => (encryptPacket_routing checksum hc key pkt).wp s
  have hs := fun id f => (setTxSkb_routing id f).wp P
  have hq := fun first state => (enqueuePerPeerTx_routing first state).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    TxRing.stepSource, hir, hp, hg, he, hs, hq, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem encryptIter_routing (checksum : Packet → M Packet) (softirq : M Unit) (need : M Bool)
    (hc : ∀ p, RetainsRoutingCall (checksum p)) (hi : RetainsRoutingCall softirq)
    (hn : RetainsRoutingCall need) : RetainsRoutingCall (encryptIter checksum softirq need) := by
  apply workerIter_routing _ _ _ _ (encryptStep_routing checksum softirq hc hi)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsRouting.refl _

theorem actualChecksum_routing (pkt : Packet) : RetainsRoutingCall (Leanux.Env.checksumHelp pkt) :=
  .of_same (routing_kernel _ (checksumHelp_sameKernel pkt))

end Leanux.Proofs.WG.AllowedIps
