import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedDisposalFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedReceive

/-! Original routing/errno/staged-splice front transport. Borrowed lookup
references change only the resident refcount; the two native splice getters
remain in order and justify their saved peer write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity TimerSlots Queues Packets
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem borrowed_timers (borrowed : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    TimerSlots.view v = TimerSlots.view w := by
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    funext pid timer
    simp only [TimerSlots.view,same]
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have current : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    funext q timer
    simp only [TimerSlots.view,current,device,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases same : pid = q
    · subst q
      simp only [ite_true,Option.map_some,resident]
      cases timer <;> rfl
    · simp only [ite_eq_right same]

private theorem borrowed_queue (borrowed : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    QueuedOccurrences.queue v = QueuedOccurrences.queue w := by
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    simp only [QueuedOccurrences.queue,same]
  | some pid =>
    obtain ⟨d,p,device,_,_,after⟩ := borrowed
    change w.dev = some d at device
    have current : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    simp only [QueuedOccurrences.queue,current,device,Option.map_some]

private theorem lookup (family addr : Nat) : StateSafe (liftWGPrefix (lookupDst family addr)) := by
  apply state_framed
  · intro initial
    apply retained_exact
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact borrowed_timers ((hoare_iff_run_ambient _ _ _).mp
      (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run)
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact borrowed_queue ((hoare_iff_run_ambient _ _ _).mp
      (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run)

private theorem trim (pid : PeerId) : StateSafe (liftWGPrefix (xmitTrim pid)) := by
  apply state_framed
  · intro initial
    unfold xmitTrim
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold xmitTrim
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' send_work_frame_step initial

private theorem splice (pid : PeerId) (packets : List Packet) :
    StateSafe (liftWGPrefix (xmitSplice pid packets)) := by
  apply state_framed
  · intro initial
    unfold xmitSplice
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold xmitSplice
    repeat' send_work_frame_step initial

theorem native_store (action : WG.M α) (frame : SameWGStore action) : StateSafe (liftWGPrefix action) :=
  state_framed action (retained_store frame) (DelayedEffects.queue_of_frame (WorkQueueFrames.store frame))

theorem front_native (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (liftWGPrefix (txFront family addr packets mtu)) := by
  apply state_native
  intro h
  let P := Inv h
  change Preserves P _
  have getter (pid : PeerId) : Preserves P (getPeer pid) := native_contract _ (by causal_delayed_native) h
  have pay (pid : Option PeerId) : Preserves P (peerPut pid) := native_contract _ (by causal_delayed_native) h
  have look : Preserves P (lookupDst family addr) := native_contract _ (lookup family addr) h
  have trimming (pid : PeerId) : Preserves P (xmitTrim pid) := native_contract _ (trim pid) h
  have splicing (pid : PeerId) (ps : List Packet) : Preserves P (xmitSplice pid ps) := native_contract _ (splice pid ps) h
  have loopback (sites : List HiddenSite) (raised : Bool) : Preserves P (loopbackSend sites raised) :=
    native_contract _ (native_store _ (loopbackSend_kernel sites raised)) h
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
    native_contract _ (native_store _ (liftRouting_sameWGStore a)) h
  have errors : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    native_contract _ (by causal_delayed_native) h
  have loop {α β : Type} (xs : List α) (initial : β) (f : α → β → WG.M (ForInStep β))
      (safe : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs initial f) :=
    list_view_spec id P xs initial f safe
  rxstack_preserves_source [txFront,txCheck,txSelect,txError,txHeaders,txWalk,
      WG.andM,branch,invariant,skipCutSites,envOk]
    using [getter,pay,look,trimming,splicing,loopback,ambient,routing,errors,loop]

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (hooks.front family addr packets mtu) := by
  change StateSafe (CausalJournal.front family addr packets mtu)
  unfold CausalJournal.front
  apply observed_native _ (txFront family addr packets mtu)
    (HandshakeSecurity.StagedConservation.Front.observed_erases Event.transmitInput Event.stagedDisposal stagedDisposal?
      (fun input run=>.old (.routed input.family input.address input.packets input.mtu run)) ⟨family,addr,packets,mtu⟩)
  · unfold HandshakeSecurity.StagedConservation.Front.observed
    apply StateAppends.bind
    · exact fun _ _ _=>⟨[_],rfl⟩
    intro _
    exact (HandshakeSecurity.StagedConservation.Front.front_appends
        (HandshakeSecurity.StagedConservation.Front.observedOps_appends _ _) _ _ _ _).receiptWGObserved _
  · exact front_native family addr packets mtu

theorem device_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply state_bind (front family addr packets mtu)
  intro selected
  cases selected with
  | error _ => exact state_pure _
  | ok pid =>
    apply state_bind (staging pid)
    intro _
    apply state_bind
    · exact peer_release _
    · intro _; exact state_pure _

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
