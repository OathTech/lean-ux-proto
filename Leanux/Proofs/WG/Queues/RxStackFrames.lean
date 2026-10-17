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


/- Reuse checked continuation factoring and fixed-predicate composition. -/
open Lean Meta Elab Tactic in
elab "rxstack_preserves_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a receive frame"
  let .app property action := target | throwError "missing action"
  let action := action.consumeMData
  if let .letE name ty value body nonDep := action then
    if name.eraseMacroScopes == `err then
      replaceMainGoal [← goal.replaceTargetDefEq
        (mkApp property (.letE `__do_jp_err ty value body nonDep))]
    evalTactic (← `(tactic| env_operation_step))
  else if action.getAppFn.isFVar then
    evalTactic (← `(tactic| env_operation_step))
  else
    throwError "not a local continuation"

macro "rxstack_preserves_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let mut use ← `(tactic| fail "no checked receive frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic| ($expand:tactic; repeat' first | rxstack_preserves_join | ($use:tactic) | rx_retention_step))

theorem loopbackSoftirq_kernel : SameWGStore loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  intro initial
  change Preserves (fun w => wgStoreView w = initial) _
  have hf : Preserves (fun w => wgStoreView w = initial) loopbackFinish :=
    loopbackFinish_sameStore.wp (fun s => s = initial)
  have hg : Preserves (fun w => wgStoreView w = initial) getDev :=
    getDev_sameWGStore.wp (fun s => s = initial)
  have read : Preserves (fun w => wgStoreView w = initial) (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => wgStoreView w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [unsupported] using [hf, hg, read, ambient]

theorem loopbackSend_kernel (sites : List HiddenSite) (raised : Bool) :
    SameWGStore (loopbackSend sites raised) := by
  unfold loopbackSend
  apply SameView.bind
  · intro initial
    exact hoare_liftAmbient (AmbientM.skipCut sites) _
  · intro _
    split
    · exact raiseLoopbackRx_sameStore.bind (fun _ => loopbackSoftirq_kernel)
    · exact SameView.pure _ _

theorem lookupDst_rxQueues (family addr : Nat) :
    SameView rxQueues (lookupDst family addr) := by
  intro initial
  change Preserves (fun w => rxQueues w = initial) _
  have hg : Preserves (fun w => rxQueues w = initial) getDev :=
    (rxQueues_kernel (project := id) getDev_sameWGStore).wp (fun s => s = initial)
  have lookup (root : Option NodeId) (bits key : Nat) :
      Preserves (fun w => rxQueues w = initial) (WG.lookup root bits key) :=
    (lookup_rxQueues root bits key).wp (fun s => s = initial)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => rxQueues w = initial) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [lookupDst, branch] using [hg, lookup, ambient]

theorem xmitTrim_rxQueues (pid : PeerId) : SameView rxQueues (xmitTrim pid) := by
  intro initial
  let P := fun w : WGWorld => rxQueues w = initial
  change Preserves P _
  have dropped : Preserves P (modifyDev fun d => { d with txDropped := d.txDropped + 1 }) :=
    (modifyDev_rxQueues (fun d => {d with txDropped := d.txDropped + 1})
      (fun _ => rfl) (fun _ => rfl)).wp (fun s => s = initial)
  unfold xmitTrim
  apply hoare_bind _ _ ((getPeer_rxQueues pid).wp (fun s => s = initial))
  intro before
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  refine hoare_bind _ _ (list_view_spec rxQueues (fun s => s = initial) _ _ _ ?_)
    (fun _ => preserves_pure ())
  intro i b
  apply hoare_bind _ _ (getPeer_rx_spec (fun s => s = initial) pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient
    (AmbientM.branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS))
    (fun w => P w ∧ CurrentRx (rxQueues w) pid p))
  intro trim
  cases trim with
  | false =>
    exact hoare_consequence (preserves_pure _)
      (fun _ h => h.1) (fun _ _ h => h)
  | true =>
    apply hoare_bind _ _ (setPeer_rx_spec (fun s => s = initial) pid {p with staged := p.staged.drop 1})
    intro _
    apply hoare_bind _ _ dropped
    intro _
    exact preserves_pure _

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
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have hg (pid : PeerId) : Preserves P (getPeer pid) :=
    (getPeer_rxQueues pid).wp (ResidentsRetained s)
  have hlookup : Preserves P (lookupDst family addr) :=
    (lookupDst_rxQueues family addr).wp (ResidentsRetained s)
  have htrim (pid : PeerId) : Preserves P (xmitTrim pid) :=
    (xmitTrim_rxQueues pid).wp (ResidentsRetained s)
  have hsplice (pid : PeerId) (packets : List Packet) : Preserves P (xmitSplice pid packets) :=
    (xmitSplice_rxQueues pid packets).wp (ResidentsRetained s)
  have hstage (pid : PeerId) : Preserves P (sendStagedPackets pid) :=
    RetainsRx.wp (sendStagedPackets_rxQueues pid) s
  have hput (pid : Option PeerId) : Preserves P (peerPut pid) :=
    RetainsRx.wp (peerPut_rxQueues pid) s
  have hloop (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    (rxQueues_kernel (loopbackSend_kernel sites raised)).wp (ResidentsRetained s)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a _
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftRouting a
    intro w route hi
    exact hi
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    (modifyDev_rxQueues (fun d => {d with txErrors := d.txErrors + 1})
      (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec rxQueues (ResidentsRetained s) xs init f hf
  have hp : Preserves P (wgXmitSource family addr packets mtu) := by
    rxstack_preserves_source [wgXmitSource, WG.andM, branch, invariant, skipCutSites, envOk]
      using [hg, hlookup, htrim, hsplice, hstage, hput, hloop, ambient, routing, errors, loop]
  apply hoare_consequence hp
  · intro w h
    change rxQueues w = s at h
    change ResidentsRetained s (rxQueues w)
    rw [h]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem reply4_rxQueues (dst : Nat) (bytes : List UInt8) :
    ProductRetainsRx (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : World => ResidentsRetained s (rxQueues w.wg)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : Leanux.M α) :=
    productRouting_spec a
      (fun store => ResidentsRetained s (fun i => store.2.2.2.dev.bind fun d => rxMap d.ifindex d.peers i))
  have hd : Preserves P (monadLift getDev : Leanux.M Device) :=
    (sameView_liftWG (fun w => rxQueues w.wg) rxQueues getDev
      (rxQueues_kernel (project := id) getDev_sameWGStore) (fun _ _ _ h => h)).wp (ResidentsRetained s)
  have hx (family addr : Nat) (packets : List Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    RetainsRx.wp (ProductRetainsRx.of_native (wgXmit_rxQueues family addr packets mtu)) s
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec (fun w : World => rxQueues w.wg) (ResidentsRetained s) a ha
  have hp : Preserves P (Leanux.Env.Stack.reply4 dst bytes) := by
    rxstack_preserves_source [Leanux.Env.Stack.reply4, skipCut, unsupported]
      using [hd, hx, ambient, routing, discarded]
  apply hoare_consequence hp
  · intro w h
    change rxQueues w.wg = s at h
    change ResidentsRetained s (rxQueues w.wg)
    rw [h]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem receive4_rxQueues (bytes : List UInt8) :
    ProductRetainsRx (Leanux.Env.Stack.receive4 bytes) := by
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : ProductRetainsRx (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    obtain ⟨e, he⟩ := failure w
    simp only [StateT.run_bind, he] at hr
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
  let P := fun w : World => ResidentsRetained s (rxQueues w.wg)
  have h4 : Preserves P (Leanux.Env.Stack.receive4 bytes) :=
    RetainsRx.wp (receive4_rxQueues bytes) s
  have h6 : Preserves P (Leanux.Env.Stack.receive6 bytes) :=
    ((stackReceive6_sameKernel bytes).of_factor
      (fun store : ProductStore43 => fun i => store.2.2.2.dev.bind fun d => rxMap d.ifindex d.peers i)
      (fun w => rxQueues w.wg) (fun _ => rfl)).wp (ResidentsRetained s)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have hp : Preserves P (Leanux.Env.deliverInner bytes) := by
    rxstack_preserves_source [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, invariant]
      using [h4, h6, ambient]
  apply hoare_consequence hp
  · intro w h
    change rxQueues w.wg = s at h
    change ResidentsRetained s (rxQueues w.wg)
    rw [h]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem stackForM_rxQueues (packets : List (List UInt8)) :
    ProductRetainsRx (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : World => ResidentsRetained s (rxQueues w.wg)
  have hi : ∀ packets : List (List UInt8), Preserves P (packets.forM Leanux.Env.deliverInner) := by
    intro xs
    induction xs with
    | nil => exact preserves_pure _
    | cons bytes xs ih =>
      simp only [List.forM_eq_forM, List.forM_cons]
      exact preserves_bind (RetainsRx.wp (deliverInner_rxQueues bytes) s) (fun _ => ih)
  apply hoare_consequence (hi packets)
  · intro w h
    change rxQueues w.wg = s at h
    change ResidentsRetained s (rxQueues w.wg)
    rw [h]
    exact rx_retained_refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.Queues
