import Leanux.Proofs.WG.Noise.PendingConsumeHistorySource
import Leanux.Proofs.WG.Noise.PendingObserverSource
import Leanux.Proofs.WG.Queues.PollPreservation
import Leanux.Proofs.WG.Queues.GroPreservation
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Queues.CurrentSlotPoll

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredRemoval

def NativeKeeps {α : Type} (a : WG.M α) : Prop :=
  ∀ seen, Preserves (fun w => NativeInv w seen) a

theorem keeps_of_parts {α : Type} (a : WG.M α)
    (configured : Preserves ConfiguredIdentity.Inv a)
    (slots : Preserves CurrentSlots.Inv a)
    (pending : PendingTickets.RetainsCall a) : NativeKeeps a := by
  intro seen
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v after hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured w ambient x v after hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots w ambient x v after hi.2.1 run,
    hi.2.2.retained ((ProjectedAction.iff_run_ambient _ _ _).mp pending w ambient x v after run)⟩

theorem keeps_store {α : Type} (a : WG.M α) (same : SameWGStore a) : NativeKeeps a := by
  intro seen
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v after hi run
  exact native_store w v seen ((ProjectedAction.iff_run_ambient _ _ _).mp same w ambient x v after run) hi

theorem keeps_packet {α : Type} (a : SkbM α) : NativeKeeps (liftSkb a) := by
  intro seen
  apply hoare_liftSkb a
  intro w d store hi hd
  refine ⟨?_,?_,?_⟩
  · simpa only [ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,
      ConfiguredIdentity.state,hd,Option.map_some] using hi.1
  · apply CurrentSlots.fields_transport hi.2.1
    unfold CurrentSlots.fields
    apply Prod.ext
    · simp only [hd,Option.map_some]
    · apply Prod.ext
      · funext pid; simp only [hd,Option.bind_some]
      · funext kid; simp only [RxCredits.keyWords,hd,Option.bind_some]
  · simpa only [PendingTickets.view,PendingTickets.pending,hd,Option.bind_some] using hi.2.2

private theorem getPeer_pending (pid : PeerId) : SameView PendingTickets.view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v after run
  exact congrArg PendingTickets.view (getPeer_normal pid w v p ambient after run).1

theorem peek_pending (pid : PeerId) : SameView PendingTickets.view (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => PendingTickets.view w = initial) _
  unfold peekRxQueue
  apply preserves_bind ((getPeer_pending pid).wp (fun s => s = initial))
  intro p
  apply preserves_bind ((PendingTickets.frame_store
    (prevQueuePeek_sameWGStore p.rxQueue)).wp (fun s => s = initial))
  intro result
  have update : Preserves (fun w => PendingTickets.view w = initial)
      (do let q ← getPeer pid; setPeer pid {q with rxQueue := result.2}) :=
    (PendingTickets.modifyPeer_spec_pending_variant pid
      (fun q => {q with rxQueue := result.2}) (fun _ => rfl)).wp (fun s => s = initial)
  simpa only [bind_assoc] using preserves_bind update (fun _ => preserves_pure result.1)

theorem drop_pending (pid : PeerId) : SameView PendingTickets.view (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  exact PendingTickets.modifyPeer_spec_pending_variant pid
    (fun p => {p with rxQueue := p.rxQueue.dropPeeked}) (fun _ => rfl)

theorem complete_pending (pid : PeerId) : SameView PendingTickets.view (completeRxQueue pid) :=
  PendingTickets.modifyPeer_spec_pending_variant pid (fun p => {p with napiScheduled := false}) (fun _ => rfl)

theorem peek_keeps (pid : PeerId) : NativeKeeps (peekRxQueue pid) :=
  keeps_of_parts _ (frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.peek_view) pid))
    (CurrentSlots.peekRxQueue_preserves pid) (PendingTickets.retained_of_frame (peek_pending pid))

theorem drop_keeps (pid : PeerId) : NativeKeeps (dropRxQueue pid) :=
  keeps_of_parts _ (frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.drop_view) pid))
    (CurrentSlots.dropRxQueue_preserves pid) (PendingTickets.retained_of_frame (drop_pending pid))

theorem complete_keeps (pid : PeerId) : NativeKeeps (completeRxQueue pid) :=
  keeps_of_parts _ (frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.complete_view) pid))
    (CurrentSlots.completeRxQueue_preserves pid) (PendingTickets.retained_of_frame (complete_pending pid))

theorem keypair_keeps (kid : Option KeypairId) (now : Bool) : NativeKeeps (keypairPut kid now) :=
  keeps_of_parts _ (frame (ConfiguredIdentity.keypairPut_view kid now))
    (CurrentSlots.keypairPut_preserves kid now) (PendingTickets.keypairPut_retained kid now)

theorem peer_keeps (pid : Option PeerId) : NativeKeeps (peerPut pid) :=
  keeps_of_parts _ (ConfiguredIdentity.peerPut_preserves pid)
    (CurrentSlots.peerPut_preserves pid) (PendingTickets.peerPut_retained pid)

theorem counter_pending (kid nonce : Nat) : SameView PendingTickets.view (counterValidate kid nonce) := by
  intro initial
  let P := fun w => PendingTickets.view w = initial
  have getter : Hoare (getKeypair kid) P
      (fun k w => P w ∧ keypairResidents w kid = some k.internalId) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v after hi run
    obtain ⟨rfl,_,d,device,resident⟩ := KeyTimes.getKeypair_return kid w v k ambient after run
    exact ⟨hi,by simp [keypairResidents,device,resident]⟩
  unfold counterValidate
  apply hoare_bind _ _ getter
  intro k
  let Q := fun w => P w ∧ keypairResidents w kid = some k.internalId
  have setter (counter : ReplayCounter) :
      Preserves Q (setKeypair kid {k with receivingCounter := counter}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v after hi run
    cases device : w.dev with
    | none => simp [Q,keypairResidents,device] at hi
    | some d =>
      cases run
      have keys : keypairResidents
          {w with dev := some {d with keypairs := d.keypairs.insert kid {k with receivingCounter := counter}}} =
          keypairResidents w := by
        funext q
        by_cases same : kid = q
        · subst q
          simpa [keypairResidents,device] using hi.2.symm
        · simp [keypairResidents,device,Std.TreeMap.getElem?_insert,same]
      have pending : PendingTickets.view
          {w with dev := some {d with keypairs := d.keypairs.insert kid {k with receivingCounter := counter}}} =
          PendingTickets.view w := by
        apply Store.ext
        · rfl
        · funext pid
          rw [PendingTickets.view_slot,PendingTickets.view_slot,keys]
          simp only [PendingTickets.nextSlots,device,Option.bind_some]
      constructor
      · simpa only [P,device,Option.map_some] using pending.trans hi.1
      · simpa only [device,Option.map_some] using (congrFun keys kid).trans hi.2
  apply hoare_consequence (P := Q) (Q := fun _ => Q) ?_ (fun _ h => h) (fun _ _ h => h.1)
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id Q)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem counter_keeps (kid nonce : Nat) : NativeKeeps (counterValidate kid nonce) :=
  keeps_of_parts _ (frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.counterValidate_view) kid nonce))
    (CurrentSlots.counterValidate_preserves kid nonce) (PendingTickets.retained_of_frame (counter_pending kid nonce))

theorem ready_keeps (first : Option SkbId) : NativeKeeps
    (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  intro seen
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact keeps_packet (SkbStore.getRx _) seen)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem state_product_store (h : List RxHistory.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : StateInv h w) : StateInv h v :=
  state_store h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same) hi


end Leanux.Proofs.WG.Noise.PendingSession
