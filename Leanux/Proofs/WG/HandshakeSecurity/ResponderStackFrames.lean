import Leanux.Proofs.WG.HandshakeSecurity.ResponderPollHistory
import Leanux.Proofs.WG.Queues.CurrentSlotStack

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes Queues

theorem wgXmit_core (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    CoreRetains (wgXmit family addr packets mtu) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Retains initial (pool w))
    (Q := fun _ w => Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Retains.refl _
  let P := fun w : WGWorld => Retains initial (pool w)
  have getter (pid : PeerId) : Preserves P (getPeer pid) :=
    (pool_of_material (getPeer_material pid)).wp (Retains initial)
  have lookup : Preserves P (lookupDst family addr) :=
    (pool_of_material (lookupDst_material family addr)).wp (Retains initial)
  have trim (pid : PeerId) : Preserves P (xmitTrim pid) :=
    (pool_of_material (xmitTrim_material pid)).wp (Retains initial)
  have splice (pid : PeerId) (packets : List Packet) : Preserves P (xmitSplice pid packets) :=
    (pool_of_material (xmitSplice_material pid packets)).wp (Retains initial)
  have stage (pid : PeerId) : Preserves P (sendStagedPackets pid) := (sendStagedPackets_core pid).wp initial
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) :=
    (pool_of_material (peerPut_material pid)).wp (Retains initial)
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    ((loopbackSend_kernel sites raised).of_factor
      (fun store : WGStoreView => pool {dev := store.dev}) pool (fun _ => rfl)).wp (Retains initial)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    ((liftRouting_sameWGStore a).of_factor
      (fun store : WGStoreView => pool {dev := store.dev}) pool (fun _ => rfl)).wp (Retains initial)
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    (pool_of_material (modifyDev_material (fun d => {d with txErrors := d.txErrors + 1}) (fun _ => rfl))).wp (Retains initial)
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rw [wgXmitSource_eq]
  change Preserves P _
  rxstack_preserves_source [wgXmitSource,WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,lookup,trim,splice,stage,pay,loopback,ambient,routing,errors,loop]

theorem wgXmit_native (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (confirmed : List Nat) : Preserves (History.Native confirmed) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  refine ⟨entry.1.retain ?_ ?_, ?_⟩
  · exact (RxCredits.KeyEffects.iff_run_ambient _ _).mp
      (RxCredits.wgXmit_keyEffect (allowed := RxCredits.NoPromotion) family addr packets mtu) w a result v b run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (wgXmit_core family addr packets mtu) w a result v b run
  · exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgXmit_preserves family addr packets mtu) w a result v b entry.2 run

theorem native_product_store {a : Leanux.M α} (same : SameProductStore a) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v entry run
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp same w x v run)
  refine ⟨Authorized.frame entry.1 ?_, CurrentSlots.fields_transport entry.2 ?_⟩
  · unfold current
    rw [device]
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem reply4_native (dst : Nat) (bytes : List UInt8) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => History.Native confirmed w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product (History.Native confirmed) _ (native_store (liftRouting_sameWGStore a) confirmed)
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product (History.Native confirmed) _ (native_store getDev_sameWGStore confirmed)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product (History.Native confirmed) _ (wgXmit_native family addr packets mtu confirmed)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_native (bytes : List UInt8) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => History.Native confirmed w.wg
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
    PublicationPoll.native_product (History.Native confirmed) _ (native_store (liftRouting_sameWGStore _) confirmed)
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
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_native _ _ confirmed)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match


theorem deliverInner_native (bytes : List UInt8) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_native bytes confirmed
  have h6 := native_product_store (stackReceive6_sameKernel bytes) confirmed
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => History.Native confirmed w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]


end Leanux.Proofs.WG.HandshakeSecurity.Responder
