import Leanux.Proofs.WG.Keypairs.Frames.EnvLeaves
import Leanux.Proofs.WG.Queues.RxCompletionFrame
import Leanux.Proofs.WG.Queues.RxPollOrder
import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.Framing.Stack

/-! Concrete stack callbacks retain the exact receive queue, device epoch
and peer identity of every surviving resident. Transmit error and cleanup
paths may delete residents; no ownership or packet-validity premise is used. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

elab "rxstack_head " n:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``ProductRetainsRx || t.isAppOf ``ProjectedAction do
    Lean.throwError "expected a receive-retention action"
  unless t.getAppArgs.size > 0 do Lean.throwError "missing action argument"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do Lean.throwError "different action head"

theorem loopbackSoftirq_kernel : SameWGStore loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  apply SameView.of_wp
  intro k
  have hf := loopbackFinish_sameStore.wp (fun s => s = k)
  mvcgen [getDev, hf, unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]

theorem loopbackSend_kernel (sites : List HiddenSite) (raised : Bool) :
    SameWGStore (loopbackSend sites raised) := by
  apply SameView.of_wp
  intro k
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => wgStoreView w = k) (fun _ w => wgStoreView w = k) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hr := raiseLoopbackRx_sameStore.wp (fun s => s = k)
  have hl := loopbackSoftirq_kernel.wp (fun s => s = k)
  mvcgen [-Std.Do.Spec.monadLift_StateT, loopbackSend, skipCut, ambient, hr, hl]

theorem lookupDst_rxQueues (family addr : Nat) :
    SameView rxQueues (lookupDst family addr) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_rxQueues root bits key).wp (fun t => t = s)
  mvcgen [lookupDst, hl, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]

theorem xmitTrim_rxQueues (pid : PeerId) : SameView rxQueues (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hd := (modifyDev_rxQueues (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) rxQueues (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem xmitSplice_rxQueues (pid : PeerId) (packets : List Packet) :
    SameView rxQueues (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_rxQueues pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl) (fun _ => rfl)

/-- Original transmit entry retains surviving receive queues on every normal
return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_rxQueues (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsRx (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := fun pid => (getPeer_rxQueues pid).wp P
  have hlookup := (lookupDst_rxQueues family addr).wp P
  have htrim := fun pid => (xmitTrim_rxQueues pid).wp P
  have hsplice := fun pid packets => (xmitSplice_rxQueues pid packets).wp P
  have hstage := fun pid => RetainsRx.wp (sendStagedPackets_rxQueues pid) s
  have hput := fun pid => RetainsRx.wp (peerPut_rxQueues pid) s
  have hloop := fun sites raised => (rxQueues_kernel (loopbackSend_kernel sites raised)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) :=
    hoare_liftAmbient a _
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) := by
    apply hoare_liftRouting a
    intro w route hi
    exact hi
  unfold Hoare at ambient routing
  have herr := (modifyDev_rxQueues (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec (m := AmbientM) rxQueues (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    hl, wgXmitSource, hg, hlookup, htrim, hsplice, hstage, hput, hloop, ambient, routing, herr,
    WG.andM, branch, invariant, unsupported, skipCutSites, envOk]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

theorem reply4_rxQueues (dst : Nat) (bytes : List UInt8) :
    ProductRetainsRx (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (rxQueues w.wg)) (fun _ w => P (rxQueues w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α)
        (fun w => P (rxQueues w.wg)) (fun _ w => P (rxQueues w.wg)) :=
    productRouting_spec a
      (fun store => P (fun i => store.2.2.2.dev.bind fun d => rxMap d.ifindex d.peers i))
  have hg : SameView rxQueues getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hd := (sameView_liftWG (fun w => rxQueues w.wg) rxQueues getDev hg
    (fun _ _ _ h => h)).wp P
  have hx (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      ⦃fun w : World => ⌜P (rxQueues w.wg)⌝⦄
        (MonadLift.monadLift (wgXmit family addr packets mtu) : Leanux.M Int)
      ⦃⇓? _ w => ⌜P (rxQueues w.wg)⌝⦄ :=
    RetainsRx.wp (ProductRetainsRx.of_native (wgXmit_rxQueues family addr packets mtu)) s
  have discardSpec (α : Type) :=
    discard_view_spec (m := Except Stop) (fun w : World => rxQueues w.wg) (α := α) P
  unfold Hoare at ambient routing
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.Stack.reply4,
    skipCut, ambient, routing, hd, hx, discardSpec, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem receive4_rxQueues (bytes : List UInt8) :
    ProductRetainsRx (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : ProductRetainsRx (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he, Except.bind] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_, rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_, rfl⟩) tail
  have excludedAlone (row : String) : ProductRetainsRx (Leanux.Env.Stack.excluded row) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : ProductRetainsRx
      (MonadLift.monadLift (MonadLift.monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    RetainsRx.of_same ((liftWG_sameProductStore _ (liftRouting_sameWGStore _)).of_factor
      (fun store : ProductStore43 => fun i => store.2.2.2.dev.bind fun d => rxMap d.ifindex d.peers i)
      (fun w => rxQueues w.wg) (fun _ => rfl))
  have read : ProductRetainsRx (getWG : Leanux.M WGWorld) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact rx_retained_refl _
  have write (f : EnvWorld → EnvWorld) : ProductRetainsRx (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact rx_retained_refl _
  have bindRule {α β : Type} {a : Leanux.M α} {f : α → Leanux.M β}
      (ha : ProductRetainsRx a) (hf : ∀ x, ProductRetainsRx (f x)) :
      ProductRetainsRx (a >>= f) := by
    intro initial
    apply hoare_consequence
      (preserves_bind (RetainsRx.wp ha initial) (fun x => RetainsRx.wp (hf x) initial))
    · intro w he
      change rxQueues w.wg = initial at he
      rw [he]
      exact rx_retained_refl _
    · intro _ _ h
      exact h
  have iteRule {α : Type} (p : Prop) [Decidable p] {a b : Leanux.M α}
      (ha : p → ProductRetainsRx a) (hb : ¬p → ProductRetainsRx b) :
      ProductRetainsRx (if p then a else b) := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  unfold ProductRetainsRx
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (rxstack_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (rxstack_head Leanux.Env.Stack.reply4; exact reply4_rxQueues _ _)
    | (rxstack_head MonadLift.monadLift; exact route _ _)
    | (rxstack_head liftM; exact route _ _)
    | (rxstack_head getWG; exact read)
    | (rxstack_head modifyEnv; exact write _)
    | (rxstack_head Pure.pure; exact RetainsRx.of_same (SameView.pure _ _))
    | (rxstack_head Bind.bind; refine bindRule ?_ ?_)
    | (rxstack_head ite; refine iteRule _ ?_ ?_)
    | keypairs_intro_forall
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_rxQueues (bytes : List UInt8) :
    ProductRetainsRx (Leanux.Env.deliverInner bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have h4 := RetainsRx.wp (receive4_rxQueues bytes) s
  have h6 := ((stackReceive6_sameKernel bytes).of_factor
    (fun store : ProductStore43 => fun i => store.2.2.2.dev.bind fun d => rxMap d.ifindex d.peers i)
    (fun w => rxQueues w.wg) (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (rxQueues w.wg)) (fun _ w => P (rxQueues w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.deliverInner,
    Leanux.Env.Stack.receive, h4, h6, invariant, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem stackForM_rxQueues (packets : List (List UInt8)) :
    ProductRetainsRx (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (rxQueues w.wg)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (rxQueues w.wg)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := RetainsRx.wp (deliverInner_rxQueues bytes) s
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  subst s
  exact rx_retained_refl _

end Leanux.Proofs.WG.Queues
