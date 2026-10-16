import Leanux.Proofs.WG.AllowedIps.RoutingRetains
import Leanux.Proofs.WG.Queues.RxTxFrames

/-! Concrete routing frames for the original staged-send helpers. Packet,
key and queue effects remain unrestricted; peer release may delete a resident.
The existing source factors and matcher environment are shared with RX frames. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem RetainsRoutingCall.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : ProjectedRetainsRoutingCall project a) (s : Option RoutingState) :
    ⦃fun w => ⌜RetainsRouting s (routingView (project w))⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsRouting s (routingView (project w))⌝⦄ :=
  ProjectedAction.wp h (RetainsRouting s) (fun _ _ hr hs => hs.trans hr)

theorem requireNotPending_routing (pid : PeerId) (why : String) :
    SameView routingView (requireNotPending pid why) :=
  SameView.pure _ _

theorem getPeer_routing (pid : PeerId) : SameView routingView (getPeer pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]

theorem getKeypair_routing (id : KeypairId) : SameView routingView (getKeypair id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, invariant, AmbientM.invariant]

theorem ownerDeref_routing (owner : IndexOwner) : SameView routingView owner.peerDeref := by
  intro s
  exact indexOwner_peerDeref_preserves owner (fun w => routingView w = s)

theorem ownerWord_routing (owner : IndexOwner) : SameView routingView owner.peerWord := by
  intro s
  exact indexOwner_peerWord_preserves owner (fun w => routingView w = s)

theorem setKeypair_routing (id : KeypairId) (k : Keypair) : SameView routingView (setKeypair id k) :=
  modifyDev_routing _ (fun _ => rfl)

theorem peerGet_routing (pid : PeerId) : SameView routingView (peerGet pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hn := (requireNotPending_routing pid "taking a reference").wp (fun t => t = s)
  mvcgen [peerGet, requireNotPending, hg, hs, refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported]
  all_goals simp_all

theorem keypairGet_routing (kp : Option KeypairId) : SameView routingView (keypairGet kp) := by
  apply SameView.of_wp
  intro s
  have hg := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [keypairGet, hg, hs, refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported]

theorem keypairPut_routing (kp : Option KeypairId) (now : Bool) :
    SameView routingView (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  have hd := fun o => indexOwner_peerDeref_preserves o (fun w => routingView w = s)
  unfold Preserves Hoare at hd
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    apply hoare_liftIndex a (fun w => routingView w = s)
    intro w d table hi hw
    unfold routingView at hi ⊢
    simpa only [hw, Option.map_some, routingState] using hi
  unfold Hoare at index_spec
  mvcgen [keypairPut, hd, index_spec, getKeypair, getDev, setKeypair, modifyDev,
    refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals dsimp only [routingView, routingState] at *; simp_all [routingState, Option.map_some, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all
  all_goals
    rename_i h
    obtain ⟨d, hd, hr⟩ := h
    exact ⟨d, hd, by simpa only [routingState, RoutingState.mk.injEq] using hr⟩

theorem sendQueuedHandshakeInitiation_routing (pid : PeerId) (retry : Bool) :
    RetainsRoutingCall (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hn := (requireNotPending_routing pid "queueing a handshake").wp P
  have hc := fun date => (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).wp (fun w => P (routingView w))
  have hget := (peerGet_routing pid).wp P
  have hput := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have hqueue := (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a (fun w => P (routingView w))
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hqueue, branch, peekQueuedUnit, recordQueued, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState])
  all_goals try assumption
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem txDevice_routing (u : TxDeviceUpdate) : SameView routingView (modifyDev u.apply) :=
  modifyDev_routing _ (fun d => by cases u <;> rfl)

theorem cpumaskChooseOnline_routing (pid : PeerId) : SameView routingView (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [cpumaskChooseOnline, hg, hs, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals trivial

theorem enqueuePerDeviceAndPeer_routing (pid : PeerId) (item : List SkbId) :
    SameView routingView (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp
  intro s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hc := fun last => (routing_kernel _ (cpumaskNextOnlineFrom_sameStore last)).wp (fun t => t = s)
  have hd := fun u => (txDevice_routing u).wp (fun t => t = s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  have queued : Hoare (queueDeviceWork .encryptWorker : WG.M Unit)
      (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) _
  unfold Hoare at queued
  mvcgen [enqueuePerDeviceAndPeer, hg, hs, hc, hcpu, hring,
    setTxSkb, skb, queued, getDev, modifyDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem enqueuePerPeerTx_routing (item : List SkbId) (state : PacketState) :
    RetainsRoutingCall (enqueuePerPeerTx item state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w)) (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hk := fun id => (getKeypair_routing id).wp P
  have hg := fun pid => (getPeer_routing pid).wp P
  have hget := fun pid => (peerGet_routing pid).wp P
  have hput := fun pid => RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  have hcpu := fun pid => (cpumaskChooseOnline_routing pid).wp P
  have hdev := fun pid => (txDevice_routing (.work pid)).wp P
  have peek (pid : PeerId) : Hoare (peekQueuedUnit .txWorker pid : WG.M Bool)
      (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) _
  have recorded (pid : PeerId) : Hoare (recordQueued .txWorker pid : WG.M Unit)
      (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) _
  unfold Hoare at peek recorded
  have howner := fun o => indexOwner_peerDeref_preserves o (fun w => P (routingView w))
  unfold Preserves Hoare at howner
  mvcgen [enqueuePerPeerTx, howner, hk, hg, hget, hput, hcpu, hdev,
    getTxSkb, setTxSkb, skb, peek, recorded, getDev, modifyDev,
    branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try assumption
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem createData_routing (pid : PeerId) (item : List SkbId) : RetainsRoutingCall (createData pid item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w)) (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hg := (getPeer_routing pid).wp P
  have hd := (enqueuePerDeviceAndPeer_routing pid item).wp P
  have hp := RetainsRoutingCall.wp (enqueuePerPeerTx_routing item .dead) s
  have hk := fun id => (keypairPut_routing id false).wp P
  have hr := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  mvcgen [createData, hg, hd, hp, hk, hr,
    getTxSkb, freeTxSkb, skb, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem stagedOutNokey_routing (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    RetainsRoutingCall (stagedOutNokey pid packets keypair invalid) := by
  cases invalid <;> cases keypair <;> apply ProjectedAction.of_wp <;> intro s
  all_goals
    let P := RetainsRouting s
    have hg := routing_getPeer P pid
    have hs := fun p => routing_setPeer P pid p
    have hk := fun id => (getKeypair_routing id).wp P
    have hset := fun id k => (setKeypair_routing id k).wp P
    have hp := fun kp => (keypairPut_routing kp false).wp P
    have hq := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
    have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) P
    simp only [stagedOutNokey, getPeer_twice, Bool.false_eq_true, ↓reduceIte]
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
      hg, hs, hk, hset, hp, hq, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem sendStagedPackets_routing (pid : PeerId) : RetainsRoutingCall (sendStagedPackets pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w)) (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := fun id => (getKeypair_routing id).wp P
  have hset := fun id k => (setKeypair_routing id k).wp P
  have hget := fun kp => (keypairGet_routing kp).wp P
  have hp := fun pid => (peerGet_routing pid).wp P
  have hout := fun packets kp invalid => RetainsRoutingCall.wp (stagedOutNokey_routing pid packets kp invalid) s
  have hput := fun kp => (keypairPut_routing kp false).wp P
  have hqueue := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  have ht := fun date => (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp (fun w => P (routingView w))
  have he := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp (fun w => P (routingView w))
  have hn (packets : List DataPacket) := mapM_view_spec routingView P newTxSkb packets
    (fun p => skb (SkbStore.newTx p))
  have hc := fun item => RetainsRoutingCall.wp (createData_routing pid item) s
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) P
  simp only [sendStagedPackets, getPeer_twice]
  have hw := fun o => indexOwner_peerDeref_preserves o (fun w => P (routingView w))
  unfold Preserves Hoare at hw
  mvcgen [hw, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
    hl, hg, hs, hk, hset, hget, hp, hout, hput, hqueue, ht, he, hn, hc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState, Option.bind_map, Function.comp_def])
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem sendKeepalive_routing (pid : PeerId) : RetainsRoutingCall (sendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have ha (p : Peer) : Hoare (hiddenAlloc .keepaliveSkb : WG.M Bool)
      (fun w => P (routingView w) ∧
        (w.dev.bind fun d => (d.peers[pid]?).map (·.allowedipsList)) = some p.allowedipsList)
      (fun _ w => P (routingView w) ∧
        (w.dev.bind fun d => (d.peers[pid]?).map (·.allowedipsList)) = some p.allowedipsList) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .keepaliveSkb) _
  unfold Hoare at ha
  have ht := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  mvcgen [sendKeepalive, hg, hs, ha, ht, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (dsimp only [routingView, routingState] at *; simp_all [routingState])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
