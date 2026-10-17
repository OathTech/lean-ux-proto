import Leanux.Proofs.WG.Packets.PublicationPoll
import Leanux.Proofs.WG.Origins.OwnerStack

/-! Concrete Stack callbacks preserve earlier packet publication anchors.
The native transmit path may release peers; all surviving full identities and
stored RX cells remain unchanged. Nested WG receive is the actual Stack Stop. -/
namespace Leanux.Proofs.WG.PublicationStack
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

private theorem lookup_geometry (family addr : Nat) :
    SameView OwnerCompletion.geometry (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    simp only [OwnerCompletion.geometry,RxCredits.rxView,same]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    have same := congrArg WGStoreView.dev hv
    change v.dev = some _ at same
    change w.dev = some d at hd
    simp only [OwnerCompletion.geometry,RxCredits.rxView,same,hd,Option.map_some,Option.bind_some]

private theorem trim_geometry (pid : PeerId) : SameView OwnerCompletion.geometry (xmitTrim pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' completion_step initial

private theorem splice_geometry (pid : PeerId) (packets : List WG.Packet) :
    SameView OwnerCompletion.geometry (xmitSplice pid packets) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold xmitSplice
  repeat' completion_step initial

/-- TX allocation does not alter the receive store or peer/key frontiers. -/
theorem wgXmit_geometry (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    SameView OwnerCompletion.geometry (wgXmit family addr packets mtu) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  rw [wgXmitSource_eq]
  have lookup : Preserves (fun w => OwnerCompletion.geometry w = initial) (lookupDst family addr) :=
    (lookup_geometry family addr).wp (fun s => s = initial)
  have trim (pid : PeerId) : Preserves (fun w => OwnerCompletion.geometry w = initial) (xmitTrim pid) :=
    (trim_geometry pid).wp (fun s => s = initial)
  have splice (pid : PeerId) (packets : List WG.Packet) :
      Preserves (fun w => OwnerCompletion.geometry w = initial) (xmitSplice pid packets) :=
    (splice_geometry pid packets).wp (fun s => s = initial)
  have stage (pid : PeerId) : Preserves (fun w => OwnerCompletion.geometry w = initial) (sendStagedPackets pid) :=
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) pid).wp (fun s => s = initial)
  have keep {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      Preserves (fun w => OwnerCompletion.geometry w = initial) a :=
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store) ha).wp (fun s => s = initial)
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact lookup)
    | (rx_retention_head xmitTrim; exact trim _)
    | (rx_retention_head xmitSplice; exact splice _ _)
    | (rx_retention_head sendStagedPackets; exact stage _)
    | (rx_retention_head loopbackSend; exact keep _ (loopbackSend_kernel _ _))
    | (allocation_release_lift_from Net.M; exact keep _ (liftRouting_sameWGStore _))
    | completion_step initial

/-- No receiving-key validity is needed to retain an already-published
packet's peer identity through a transmit reply and its final payment. -/
theorem wgXmit_peers (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) (initial) :
    Preserves (PeersRetained initial) (wgXmit family addr packets mtu) := by
  have keep {α : Type} (a : WG.M α) (ha : SameView ConfiguredIdentity.view a) :
      Preserves (PeersRetained initial) a :=
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured) ha initial
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst
       exact keep _ ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.lookupDst_view) _ _))
    | (rx_retention_head xmitTrim
       exact keep _ ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitTrim_view) _))
    | (rx_retention_head xmitSplice
       exact keep _ ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitSplice_view) _ _))
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_peers _ initial)
    | (rx_retention_head loopbackSend
       exact keep _ (ConfiguredIdentity.sameWG (project := id) (loopbackSend_kernel _ _)))
    | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ hi => hi))
    | publication_peer_step initial

theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (wgXmit family addr packets mtu) :=
  preserves_of_frames _ ((wgXmit_geometry family addr packets mtu).factor Prod.snd)
    (wgXmit_peers family addr packets mtu) history

private theorem store {α : Type} (a : WG.M α) (frame : SameWGStore a) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) a :=
  (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.store) a frame history

private theorem product_store {α : Type} (a : Leanux.M α) (frame : SameProductStore a)
    (history : List RxHistory.Event) : Preserves (fun w : World => PublicationHistory.Inv history w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have fields := (ProjectedAction.iff_run _ _ _).mp frame w result v hr
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) fields
  have packets : RxDisposition.nativeRxStore v.wg = RxDisposition.nativeRxStore w.wg := by
    simp only [RxDisposition.nativeRxStore,dev]
  have peers : CurrentIdentity.peerView v.wg = CurrentIdentity.peerView w.wg := by
    simp only [CurrentIdentity.peerView,dev]
  apply hi.transport
  · intro id pkt hp _
    exact ⟨(congrFun (congrArg Prod.snd packets) id).symm.trans hp,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst packets)⟩
  · apply peers_fields
    intro pid ident resident
    simpa only [peers] using resident

theorem reply4_preserves (dst : Nat) (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => PublicationHistory.Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ (store _ (liftRouting_sameWGStore a) history)
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (store _ getDev_sameWGStore history)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product _ _ (wgXmit_preserves family addr packets mtu history)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_preserves (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => PublicationHistory.Inv history w.wg
  have stopped (a : Leanux.M Unit) (hs : ∀ w, ∃ e, a.run w = .error e)
      (next : Unit → Leanux.M Unit) : Preserves P (a >>= next) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.stopped_bind) a hs next P
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
    PublicationPoll.native_product _ _ (store _ (liftRouting_sameWGStore _) history)
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
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves _ _ history)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_preserves (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes history
  have h6 := product_store _ (stackReceive6_sameKernel bytes) history
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => PublicationHistory.Inv history w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

theorem stack_preserves (packets : List (List UInt8)) (history : List RxHistory.Event) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes history) (fun _ => ih)

theorem poll_stack (pid : PeerId) (budget : Nat) (history : List RxHistory.Event) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg)
      (rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)) :=
  PublicationPoll.poll pid budget _ history (fun packets => stack_preserves packets history)

end Leanux.Proofs.WG.PublicationStack
