import Leanux.Proofs.WG.Queues.TxStagedHead
import Leanux.Proofs.WG.Queues.CurrentSlotStack
import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.WG.Lifetimes.AllocationAmbient

/-! Actual transmit and Stack calls retain an already resident TX head.
Packet allocation validity is transported by the existing allocation observer. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.StackHead
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private abbrev Ready (target : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  Packets.Inv w ∧ HeadState target state w

private theorem store_ready (target : SkbId) (state : PacketState)
    (a : WG.M α) (frame : SameWGStore a) : Preserves (Ready target state) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi run
  have hv := (ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v ambient' run
  have hd := congrArg WGStoreView.dev hv
  change v.dev = w.dev at hd
  simpa only [Ready,Packets.Inv,Packets.snapshot,HeadState,txPackets,hd] using hi

private theorem lookup (target : SkbId) (state : PacketState) (family addr : Nat) :
    Preserves (Ready target state) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have hd := congrArg WGStoreView.dev borrowed
    change v.dev = w.dev at hd
    simpa only [Ready,Packets.Inv,Packets.snapshot,HeadState,txPackets,hd] using hi
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    change w.dev = some d at hd
    have dev := congrArg WGStoreView.dev hv
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at dev
    simpa only [Ready,Packets.Inv,Packets.snapshot,Packets.deviceStore,HeadState,
      txPackets,dev,hd,Option.bind_some] using hi

private theorem trim (target : SkbId) (state : PacketState) (pid : PeerId) :
    Preserves (Ready target state) (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' staged_head_base target, state

private theorem splice (target : SkbId) (state : PacketState) (pid : PeerId)
    (packets : List WG.Packet) : Preserves (Ready target state) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' staged_head_base target, state

/-- The completed original transmit front preserves the saved head and the
allocation frontier needed by the subsequent fresh staging. -/
theorem front (family addr : Nat) (packets : List WG.Packet) (mtu target : Nat)
    (state : PacketState) : Preserves (Ready target state) (Packets.txFront family addr packets mtu) := by
  let P := Ready target state
  have getPeerRule := (pinned_const _private.Leanux.Proofs.WG.Queues.TxStagedHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StagedHead.read_peer) target state
  have pay := (pinned_const _private.Leanux.Proofs.WG.Queues.TxStagedHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StagedHead.peer_put) target state
  have look := lookup target state family addr
  have trim := trim target state
  have splice := splice target state
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    store_ready target state _ (loopbackSend_kernel sites raised)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    store_ready target state _ (liftRouting_sameWGStore a)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) := by
    staged_head_base target, state
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rxstack_preserves_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getPeerRule,look,trim,splice,pay,loopback,ambient,routing,errors,loop]

/-- The full native transmit, including normal negative statuses and nullable
final peer payment, retains an old head. No head is read from a later state. -/
theorem wgXmit_head (family addr : Nat) (packets : List WG.Packet) (mtu target : Nat)
    (state : PacketState) :
    Hoare (wgXmit family addr packets mtu) (fun w=>Packets.Inv w ∧ HeadState target state w)
      (fun _=>HeadState target state) := by
  rw [Packets.wgXmit_front_factor]
  apply hoare_bind _ _ (front family addr packets mtu target state)
  intro result
  cases result with
  | error err => exact hoare_consequence (preserves_pure err) (fun _ h=>h.2) (fun _ _ h=>h)
  | ok pid =>
    unfold Packets.txTail
    apply hoare_bind _ _ (StagedHead.send pid target state)
    intro _
    apply preserves_bind
      ((peerPut_packets (some pid)).wp (fun s=>∃p,s target=some p ∧ p.state=state))
    intro _
    exact preserves_pure 0

/-- An existing allocation journal witnesses the state validity used between
real Stack calls. This predicate introduces no executable observation. -/
def Inv (target : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  (∃ h, AllocationInv h w) ∧ HeadState target state w

private theorem bounded (hi : AllocationInv h w) : Packets.Inv w := by
  cases hd:w.dev with
  | none =>
    intro i stamp atSlot
    simp [Packets.snapshot,hd] at atSlot
  | some d => simpa only [Packets.Inv,Packets.snapshot,hd] using hi.packetBounded d hd

private theorem observed_allocation (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a)
    (keep : StatePrefixPreserves (fun h w _=>AllocationInv h w) LifetimeEvent.Safe g) :
    Preserves (fun w=>∃h,AllocationInv h w) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi run
  obtain ⟨h,hi⟩ := hi
  obtain ⟨_,_,_,out⟩ := keep w ambient h hi
  have er := erase w ambient h
  rw [run] at er
  exact ⟨(runStatePrefix g w ambient h).2,by simpa only [runStatePrefix,er] using out⟩

/-- The existing R2 allocation observer transports validity across the same
native transmit execution that preserves the saved head. -/
theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu target : Nat)
    (state : PacketState) : Preserves (Inv target state) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have alloc := (hoare_iff_run_ambient _ _ _).mp
    (observed_allocation (wgXmitPrefix family addr packets mtu) _
      (wgXmitPrefix_erases family addr packets mtu)
      (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit family addr packets mtu))
    w a result v b hi.1 run
  obtain ⟨h,halloc⟩ := hi.1
  exact ⟨alloc,(hoare_iff_run_ambient _ _ _).mp
    (wgXmit_head family addr packets mtu target state) w a result v b
    ⟨bounded halloc,hi.2⟩ run⟩

private theorem native_store (target : SkbId) (state : PacketState)
    (a : WG.M α) (same : SameWGStore a) : Preserves (Inv target state) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi run
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w ambient result v ambient' run
  obtain ⟨h,ha⟩ := hi.1
  have hd := congrArg WGStoreView.dev eq
  change v.dev=w.dev at hd
  exact ⟨⟨h,ha.store eq⟩,by simpa only [HeadState,txPackets,hd] using hi.2⟩

private theorem product_store (target : SkbId) (state : PacketState)
    (a : Leanux.M α) (same : SameProductStore a) :
    Preserves (fun w:World=>Inv target state w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have eq := congrArg (fun s:ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run)
  change wgStoreView v.wg=wgStoreView w.wg at eq
  have hd := congrArg WGStoreView.dev eq
  change v.wg.dev=w.wg.dev at hd
  obtain ⟨h,ha⟩ := hi.1
  exact ⟨⟨h,ha.store eq⟩,by simpa only [HeadState,txPackets,hd] using hi.2⟩

theorem reply4_preserves (target : SkbId) (state : PacketState) (dst : Nat) (bytes : List UInt8) :
    Preserves (fun w : World => Inv target state w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => Inv target state w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product (Inv target state) _ (native_store target state _ (liftRouting_sameWGStore a))
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product (Inv target state) _ (native_store target state _ getDev_sameWGStore)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product (Inv target state) _ (wgXmit_preserves family addr packets mtu target state)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_preserves (target : SkbId) (state : PacketState) (bytes : List UInt8) :
    Preserves (fun w : World => Inv target state w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => Inv target state w.wg
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
    PublicationPoll.native_product (Inv target state) _ (native_store target state _ (liftRouting_sameWGStore _))
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
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves target state _ _)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match


theorem deliverInner_preserves (target : SkbId) (state : PacketState) (bytes : List UInt8) :
    Preserves (fun w : World => Inv target state w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves target state bytes
  have h6 := product_store target state _ (stackReceive6_sameKernel bytes)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv target state w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

theorem stack_preserves (target : SkbId) (state : PacketState) (packets : List (List UInt8)) :
    Preserves (fun w : World => Inv target state w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves target state bytes) (fun _ => ih)

end Leanux.Proofs.WG.Queues.TxDisposition.StackHead
