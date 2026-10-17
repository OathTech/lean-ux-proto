import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.TxDisposition
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

abbrev ProductRetainsRoutingCall (a : Leanux.M α) : Prop :=
  ProjectedRetainsRoutingCall World.wg a

theorem RetainsRoutingCall.liftWG {a : WG.M α} (h : RetainsRoutingCall a) :
    ProductRetainsRoutingCall (Leanux.liftWG a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (ProjectedAction.iff_run_ambient _ _ _).mp h _ _ _ _ _ he

private theorem borrowed_routing
    (hb : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    routingView v = routingView w := by
  cases result with
  | none =>
    have hd := congrArg WGStoreView.dev hb
    simpa only [wgStoreView, routingView] using congrArg (Option.map routingState) hd
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    have hv := congrArg WGStoreView.dev hk
    simp only [wgStoreView] at hd hv
    simp [routingView, hv, hd, hs]

theorem lookup_routing (root : Option NodeId) (bits key : Nat) :
    SameView routingView (lookup root bits key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookup_spec root bits key (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupSrc_routing (protocol : Nat) (bytes : List UInt8) :
    SameView routingView (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem lookupDst_routing (family addr : Nat) : SameView routingView (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact borrowed_routing ((hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w ambient result v ambient' rfl hr)

theorem sendSkbToPeer_routing (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView routingView (sendSkbToPeer pid bytes ds) := by
  apply SameView.of_wp
  intro s
  have hp := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have h4 := fun e => (send4_routing e (some pid) bytes ds true).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e (some pid) bytes ds true).wp (fun t => t = s)
  mvcgen [sendSkbToPeer, hp, hs, h4, h6, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem timersDataSent_routing (pid : PeerId) : SameView routingView (timersDataSent pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_routing pid).wp (fun t => t = s)
  have hj := (jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).wp (fun w => routingView w = s)
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_routing pid .newHandshake n jc).wp (fun t => t = s)
  have hc := (callerJiffies_sameWGWorld .timerJiffiesDataSent).wp (fun w => routingView w = s)
  mvcgen [timersDataSent, hp, hj, hg, ha, hc, branch, AmbientM.branch]

theorem keepKeyFresh_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFresh pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := (getPeer_routing pid).wp P
  have hk := fun id => (getKeypair_routing id).wp P
  have he := fun d birth age => (branchExpired_sameWGWorld d birth age).wp (fun w => P (routingView w))
  have hh := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  mvcgen [keepKeyFresh, hp, hk, he, hh, WG.andM, WG.orM, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant]
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
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w)) (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hs := fun bytes ds => (sendSkbToPeer_routing pid bytes ds).wp P
  have hd := (timersDataSent_routing pid).wp P
  have hk := RetainsRoutingCall.wp (keepKeyFresh_routing pid) s
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    createDataDone, ht, ha, getTxSkb, skb, hs, hd, hk, WG.andM, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
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
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => P (routingView w)) (fun _ w => P (routingView w)) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  unfold Hoare at skb
  have hq := fun (q : PrevQueue (List SkbId)) => (routing_kernel _ (prevQueuePeek_sameWGStore q)).wp P
  have hd := fun item => RetainsRoutingCall.wp (createDataDone_routing pid item) s
  have hk := fun kp => (keypairPut_routing kp false).wp P
  have hu := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) P
  simp only [TxDisposition.stepSource, TxDisposition.bodySource, TxDisposition.disposeSource, getPeer_twice]
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hs, getTxSkb, skb, hq, hd, freeTxSkb, hk, hu, WG.andM, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem workerIter_routing (worker : Worker) (pid : Option Nat) (step afterItem : Leanux.M Bool)
    (hs : ProductRetainsRoutingCall step) (ha : ProductRetainsRoutingCall afterItem) :
    ProductRetainsRoutingCall (workerIter worker pid step afterItem) := by
  apply ProjectedAction.of_wp
  intro s
  have hstep := RetainsRoutingCall.wp hs s
  have hafter := RetainsRoutingCall.wp ha s
  mvcgen [workerIter, hstep, hafter]
  subst s
  exact RetainsRouting.refl _

theorem txIter_routing (pid : PeerId) (need : Leanux.M Bool) (hn : ProductRetainsRoutingCall need) :
    ProductRetainsRoutingCall (txIter pid need) := by
  apply workerIter_routing _ _ _ _ (RetainsRoutingCall.liftWG (txStep_routing pid))
  apply ProjectedAction.of_wp
  intro s
  have hneed := RetainsRoutingCall.wp hn s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, hneed, branch, ambient]
  subst s
  exact RetainsRouting.refl _

theorem xmitTrim_routing (pid : PeerId) : SameView routingView (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_routing (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView]

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
  have hstage := fun pid => RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have hput := fun pid => RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  have hloop := fun sites raised => (routing_kernel _ (loopbackSend_kernel sites raised)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  unfold Hoare at ambient routing
  have herr := (modifyDev_routing (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT, hl, wgXmitSource,
    hg, hlookup, htrim, hsplice, hstage, hput, hloop, ambient, routing, herr, skipCutSites, envOk,
    WG.andM, branch, invariant, unsupported, AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | trivial

theorem reply4_routing (dst : Nat) (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productRouting_spec a
      (fun store => P (store.2.2.2.dev.map routingState))
  have hg : SameView routingView getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hd := (sameView_liftWG (fun w => routingView w.wg) routingView getDev hg
    (fun _ _ _ h => h)).wp P
  have hx (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      ⦃fun w : World => ⌜P (routingView w.wg)⌝⦄
        (MonadLift.monadLift (wgXmit family addr packets mtu) : Leanux.M Int)
      ⦃⇓? _ w => ⌜P (routingView w.wg)⌝⦄ :=
    RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (wgXmit_routing family addr packets mtu)) s
  have discardSpec (α : Type) :=
    discard_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) P
  unfold Hoare at ambient routing
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.Stack.reply4,
    skipCut, ambient, routing, hd, hx, discardSpec, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem receive4_routing (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : ProductRetainsRoutingCall (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have excludedAlone (row : String) : ProductRetainsRoutingCall (Leanux.Env.Stack.excluded row) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : ProductRetainsRoutingCall
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    ProjectedRetainsRoutingCall.of_same ((liftWG_sameProductStore _ (liftRouting_sameWGStore _)).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w => routingView w.wg) (fun _ => rfl))
  have read : ProductRetainsRoutingCall (getWG : Leanux.M WGWorld) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact RetainsRouting.refl _
  have write (f : EnvWorld → EnvWorld) : ProductRetainsRoutingCall (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact RetainsRouting.refl _
  have bindRule {α β : Type} {a : Leanux.M α} {f : α → Leanux.M β}
      (ha : ProductRetainsRoutingCall a) (hf : ∀ x, ProductRetainsRoutingCall (f x)) :
      ProductRetainsRoutingCall (a >>= f) := by
    intro initial
    apply hoare_consequence
      (preserves_bind (RetainsRoutingCall.wp ha initial) (fun x => RetainsRoutingCall.wp (hf x) initial))
    · intro w he
      change routingView w.wg = initial at he
      rw [he]
      exact RetainsRouting.refl _
    · intro _ _ h
      exact h
  have iteRule {α : Type} (p : Prop) [Decidable p] {a b : Leanux.M α}
      (ha : p → ProductRetainsRoutingCall a) (hb : ¬p → ProductRetainsRoutingCall b) :
      ProductRetainsRoutingCall (if p then a else b) := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  unfold ProductRetainsRoutingCall ProjectedRetainsRoutingCall
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (unfold ProductRetainsRoutingCall ProjectedRetainsRoutingCall)
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (rxstack_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (rxstack_head Leanux.Env.Stack.reply4; exact reply4_routing _ _)
    | (rxstack_head MonadLift.monadLift; exact route _ _)
    | (rxstack_head liftM; exact route _ _)
    | (rxstack_head getWG; exact read)
    | (rxstack_head modifyEnv; exact write _)
    | (rxstack_head Pure.pure; exact ProjectedRetainsRoutingCall.of_same (SameView.pure _ _))
    | (rxstack_head Bind.bind; refine bindRule ?_ ?_)
    | (rxstack_head ite; refine iteRule _ ?_ ?_)
    | keypairs_intro_forall
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_routing (bytes : List UInt8) :
    ProductRetainsRoutingCall (Leanux.Env.deliverInner bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have h4 := RetainsRoutingCall.wp (receive4_routing bytes) s
  have h6 := ((stackReceive6_sameKernel bytes).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.deliverInner,
    Leanux.Env.Stack.receive, h4, h6, invariant, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem stackForM_routing (packets : List (List UInt8)) :
    ProductRetainsRoutingCall (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (routingView w.wg)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (routingView w.wg)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := RetainsRoutingCall.wp (deliverInner_routing bytes) s
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  subst s
  exact RetainsRouting.refl _


theorem encryptPacket_routing (checksum : Packet → Leanux.M Packet)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (key : KeypairId) (pkt : DataPacket) :
    ProductRetainsRoutingCall (encryptPacket checksum key pkt) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have hpad := (sameView_liftWG (fun w => routingView w.wg) routingView
    (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu)
    ((calculateSkbPadding_sameWGWorld pkt.plaintext.bytes.length pkt.plaintext.mtu).of_factor
      routingView routingView (fun _ => rfl)) (fun _ _ _ h => h)).wp P
  have hchecksum := fun p => RetainsRoutingCall.wp (hc p) s
  have hkey := (sameView_liftWG (fun w => routingView w.wg) routingView
    (getKeypair key) (getKeypair_routing key) (fun _ _ _ h => h)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, encryptPacket, skipCut, hiddenAlloc,
    ambient, hpad, hchecksum, hkey, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem encryptPoll_routing : SameView routingView TxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have hm := fun ring => (modifyDev_routing (fun d => {d with encryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [TxRing.pollSource, hm, getDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem encryptStep_routing (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (hi : ProductRetainsRoutingCall softirq) :
    ProductRetainsRoutingCall (encryptStep checksum softirq) := by
  rw [← TxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hir := RetainsRoutingCall.wp hi s
  have hp := (sameView_liftWG (fun w => routingView w.wg) routingView
    TxRing.pollSource encryptPoll_routing (fun _ _ _ h => h)).wp P
  have poll : Hoare (liftWG TxRing.pollSource)
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) := hp
  unfold Hoare at poll
  have nativeSkb {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have skb {α : Type} (a : SkbM α) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView
      (liftSkb a) (nativeSkb a) (fun _ _ _ h => h)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have he := fun key pkt => RetainsRoutingCall.wp (encryptPacket_routing checksum hc key pkt) s
  have hq (first : List SkbId) (state : PacketState) :
      Hoare (MonadLift.monadLift (enqueuePerPeerTx first state) : Leanux.M Unit)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (enqueuePerPeerTx_routing first state)) s
  unfold Hoare at hq
  have hl (α β : Type) := list_view_spec (m := Except Stop)
    (fun w : World => routingView w.wg) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT, hl,
    TxRing.stepSource, hir, poll, getTxSkb, skb, he, setTxSkb, hq, ambient, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem encryptIter_routing (checksum : Packet → Leanux.M Packet) (softirq : Leanux.M Unit) (need : Leanux.M Bool)
    (hc : ∀ p, ProductRetainsRoutingCall (checksum p)) (hi : ProductRetainsRoutingCall softirq)
    (hn : ProductRetainsRoutingCall need) : ProductRetainsRoutingCall (encryptIter checksum softirq need) := by
  apply workerIter_routing _ _ _ _ (encryptStep_routing checksum softirq hc hi)
  apply ProjectedAction.of_wp
  intro s
  have hneed := RetainsRoutingCall.wp hn s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, hneed, branch, ambient]
  subst s
  exact RetainsRouting.refl _

theorem actualChecksum_routing (pkt : Packet) : ProductRetainsRoutingCall (Leanux.Env.checksumHelp pkt) :=
  ProjectedRetainsRoutingCall.of_same
    ((checksumHelp_sameWorld pkt).of_factor
      (fun w : World => routingView w.wg)
      (fun w => routingView w.wg) (fun _ => rfl))

end Leanux.Proofs.WG.AllowedIps
