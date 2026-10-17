import Leanux.Proofs.WG.Queues.CurrentSlotPoll
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! Three-slot compatibility is preserved through the actual Stack callback, including its
transmit path and nullable final peer payment. Excluded nested receive paths
retain their original Stops. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem lookupDst_view (family addr : Nat) :
    SameView Affiliation.view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl hr
  change (wgStoreView v).dev.map Affiliation.state = (wgStoreView w).dev.map Affiliation.state
  cases result with
  | none => change wgStoreView v = wgStoreView w at borrowed; rw [borrowed]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    simp only [hv,hd,Option.map_some]
    exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount := p.refcount+1} hp rfl)

private theorem trim_preserves (pid : PeerId) : Preserves Inv (xmitTrim pid) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec fields (fun s => s = initial)
       intro x b
       change Preserves (fun w => fields w = initial) _)
    | slot_fields_step initial

private theorem splice_preserves (pid : PeerId) (packets : List WG.Packet) :
    Preserves Inv (xmitSplice pid packets) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold xmitSplice
  repeat' slot_fields_step initial

/-- Both ordinary negative status returns and successful sends preserve the
slot invariant. Source failures and final peer release remain possible. -/
theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves Inv (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  have getPeerRule (pid : PeerId) : Preserves Inv (getPeer pid) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.getPeer_frame) pid
  have lookup : Preserves Inv (lookupDst family addr) :=
    view_preserves (project := id) (lookupDst_view family addr)
  have trim (pid : PeerId) : Preserves Inv (xmitTrim pid) := trim_preserves pid
  have splice (pid : PeerId) (packets : List WG.Packet) : Preserves Inv (xmitSplice pid packets) :=
    splice_preserves pid packets
  have stage (pid : PeerId) : Preserves Inv (sendStagedPackets pid) :=
    sendStagedPackets_preserves pid
  have pay (pid : Option PeerId) : Preserves Inv (peerPut pid) := peerPut_preserves pid
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves Inv (loopbackSend sites raised) :=
    store_preserves (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a Inv
  have routing {α : Type} (a : Net.M α) : Preserves Inv (monadLift a : WG.M α) :=
    store_preserves (liftRouting_sameWGStore a)
  have errors : Preserves Inv (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
by
      slot_traffic_step
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves Inv (f x b)) : Preserves Inv (forIn xs init f) :=
    list_view_spec id Inv xs init f hf
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]


theorem reply4_preserves (dst : Nat) (bytes : List UInt8) :
    Preserves (fun w : World => Inv w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => Inv w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product Inv _ (store_preserves (liftRouting_sameWGStore a))
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product Inv _ (store_preserves getDev_sameWGStore)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product Inv _ (wgXmit_preserves family addr packets mtu)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_preserves (bytes : List UInt8) :
    Preserves (fun w : World => Inv w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => Inv w.wg
  have stopped (a : Leanux.M Unit) (failure : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : Preserves P (a >>= tail) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := failure w
    simp only [StateT.run_bind,he] at hr
    contradiction
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_,rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_,rfl⟩) tail
  have excludedAlone (row : String) : Preserves P (Leanux.Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : Preserves P
      (monadLift (monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    PublicationPoll.native_product Inv _ (store_preserves (liftRouting_sameWGStore _))
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (allocation_release_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves _ _)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match


theorem deliverInner_preserves (bytes : List UInt8) :
    Preserves (fun w : World => Inv w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes
  have h6 := product_store_preserves (stackReceive6_sameKernel bytes)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

theorem stack_preserves (packets : List (List UInt8)) :
    Preserves (fun w : World => Inv w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes) (fun _ => ih)

theorem poll_stack (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World => Inv w.wg)
      (rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)) :=
  poll_preserves pid budget _ stack_preserves

end Leanux.Proofs.WG.CurrentSlots
