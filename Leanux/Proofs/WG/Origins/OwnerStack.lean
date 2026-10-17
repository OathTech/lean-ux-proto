import Leanux.Proofs.WG.Origins.OwnerControls
import Leanux.Proofs.WG.Origins.OwnerPoll
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! The concrete stack callback preserves the receiving-owner carrier. Nested
WireGuard UDP reception is an explicit source Stop; the TCP reply enters the
actual transmit path, whose TX allocation does not change RX key references. -/
namespace Leanux.Proofs.WG.OwnerStack
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerControls

private theorem lookupDst_preserves (family addr : Nat) :
    Preserves Carrier (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi (congrArg WGStoreView.dev borrowed)
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    have same := congrArg WGStoreView.dev hv
    change v.dev = some _ at same
    change w.dev = some d at hd
    have mapped := (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_map)
      (fun old => {old with peers := old.peers.insert pid {p with refcount := p.refcount + 1}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev) mapped
    simpa only [hd,Option.map_some] using same

private theorem trim_preserves (pid : PeerId) : Preserves Carrier (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' owner_control_step

private theorem splice_preserves (pid : PeerId) (packets : List WG.Packet) :
    Preserves Carrier (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' owner_control_step

/-- Both ordinary negative status returns and successful sends retain the
carrier. Source failures and final peer release remain possible. -/
theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves Carrier (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  have getPeerRule (pid : PeerId) : Preserves Carrier (getPeer pid) := readPeer pid
  have lookup : Preserves Carrier (lookupDst family addr) := lookupDst_preserves family addr
  have trim (pid : PeerId) : Preserves Carrier (xmitTrim pid) := trim_preserves pid
  have splice (pid : PeerId) (packets : List WG.Packet) : Preserves Carrier (xmitSplice pid packets) :=
    splice_preserves pid packets
  have stage (pid : PeerId) : Preserves Carrier (sendStagedPackets pid) :=
    OwnerCompletion.sendStagedPackets_preserves pid
  have pay (pid : Option PeerId) : Preserves Carrier (peerPut pid) := OwnerConsume.peerPut_preserves pid
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves Carrier (loopbackSend sites raised) :=
    store _ (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves Carrier (monadLift a : WG.M α) :=
    hoare_liftAmbient a Carrier
  have routing {α : Type} (a : Net.M α) : Preserves Carrier (monadLift a : WG.M α) :=
    store _ (liftRouting_sameWGStore a)
  have errors : Preserves Carrier (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    modifyDevice _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves Carrier (f x b)) : Preserves Carrier (forIn xs init f) :=
    list_view_spec id Carrier xs init f hf
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]

private theorem native_product {α : Type} (a : WG.M α) (ha : Preserves Carrier a) :
    Preserves (fun w : World => Carrier w.wg) (liftWG a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.native_product) a ha

theorem reply4_preserves (dst : Nat) (bytes : List UInt8) :
    Preserves (fun w : World => Carrier w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => Carrier w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : Leanux.M α) :=
    native_product _ (store _ (liftRouting_sameWGStore a))
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    native_product _ (store _ getDev_sameWGStore)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    native_product _ (wgXmit_preserves family addr packets mtu)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_preserves (bytes : List UInt8) :
    Preserves (fun w : World => Carrier w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => Carrier w.wg
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
    native_product _ (store _ (liftRouting_sameWGStore _))
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

private theorem product_store {α : Type} (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (fun w : World => Carrier w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have eq := (ProjectedAction.iff_run _ _ _).mp frame w result v hr
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
    hi (congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq)

theorem deliverInner_preserves (bytes : List UInt8) :
    Preserves (fun w : World => Carrier w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes
  have h6 := product_store _ (stackReceive6_sameKernel bytes)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Carrier w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

theorem stack_preserves (packets : List (List UInt8)) :
    Preserves (fun w : World => Carrier w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes) (fun _ => ih)

theorem poll_stack (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World => Carrier w.wg)
      (rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)) :=
  OwnerPoll.poll pid budget _ stack_preserves

end Leanux.Proofs.WG.OwnerStack
