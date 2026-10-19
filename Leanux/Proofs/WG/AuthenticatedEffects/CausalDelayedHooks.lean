import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueDataFrames

/-! Actual shared-driver key/packet callbacks retain live delayed occurrences.
Their old journal receipts remain intact; native endpoint frames are used only
for these same callbacks, never to join separately executed histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity HandshakeSecurity TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem projected_erases {E F α : Type} (body : WGPrefix E α) (native : WG.M α)
    (ρ : E → Option F) (projects : StateProjectsPrefix ρ id body (liftWGPrefix native)) :
    ErasesStatePrefix body native := by
  intro w a h
  have projected := congrArg Prod.fst (projects w a h)
  have maps : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext ⟨⟨value,v⟩,b⟩
    rfl
  change ((native.run w).run a) =
    (runWGPrefix body w a h).1.map (fun x => (Prod.map id id x.1,x.2)) at projected
  rw [maps,Except.map_id] at projected
  exact projected.symm

theorem old_state (body : WGPrefix Journal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native)
    (safe : StateSafe (liftWGPrefix native)) : StateSafe (state body) :=
  observed_native _ native (focusStatePrefix_erases Event.old old? erases)
    (StateAppends.focus Event.old old? body) safe

private theorem selection_native (pid : PeerId) : StateSafe (liftWGPrefix (Responder.selectionPrefix pid)) := by
  apply state_framed
  · intro initial
    unfold Responder.selectionPrefix
    simp only [branch]
    repeat' first
      | (rx_retention_head keypairGet; exact keypairGet_retained _ initial)
      | timer_data_step initial
  · change SameView SendWorkCauses.queue _
    intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold Responder.selectionPrefix
    simp only [branch]
    repeat' first
      | (rx_retention_head keypairGet; exact (SendWorkCauses.key_get_frame _).wp (fun q => q = initial))
      | queue_callback_step initial

theorem selection (pid : PeerId) : StateSafe (hooks.selection pid) :=
  observed_native _ _
    (RetirementSecurity.NestedPeerRelease.projects_erases old? (CausalJournal.selection_projects pid)
      (focusStatePrefix_erases _ _ (Responder.DriverCuts.selection_erases pid)))
    (CallbackQuiet.selection (fun _ : Event => (none : Option Empty)) (fun _ => rfl) (fun _ _ => rfl) pid).1
    (selection_native pid)

private theorem confirmation_native (pid : PeerId) (kid : KeypairId) :
    StateSafe (liftWGPrefix (receivedWithKeypair pid kid)) := by
  apply state_framed
  · intro initial
    unfold receivedWithKeypair
    index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
    simp only [branch]
    repeat' timer_data_step initial
  · change SameView SendWorkCauses.queue _
    intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold receivedWithKeypair
    index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
    simp only [branch]
    repeat' first
      | (rx_retention_head keypairPut; exact (SendWorkCauses.of_workQueueFrame (Queues.WorkQueueFrames.keypairPut_frame _ _)).wp (fun q => q = initial))
      | queue_callback_step initial

theorem confirmation (pid : PeerId) (kid : KeypairId) : StateSafe (hooks.confirmation pid kid) :=
  old_state _ _ (focusStatePrefix_erases _ _ (Responder.DriverCuts.confirmation_erases pid kid))
    (confirmation_native pid kid)

theorem session (pid : PeerId) : StateSafe (hooks.session pid) := by
  apply state_receipt
  apply old_state _ _ (focusStatePrefix_erases _ _ (Responder.DriverCuts.session_erases pid))

  exact state_framed _ (beginSession_retained pid) (SendWorkCauses.session_frame pid)

private theorem reserve_native (slot : KeypairId) : StateSafe (liftWGPrefix (Nonce.reserveNative slot)) := by
  unfold Nonce.reserveNative
  causal_delayed_native

theorem reserve (slot : KeypairId) : StateSafe (hooks.reserve slot) := by
  apply old_state _ _
    (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases slot)) _)
  exact reserve_native slot

theorem allocate (packets : List DataPacket) : StateSafe (hooks.allocate packets) := by
  apply old_state _ _ (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  apply state_framed
  · intro initial
    apply mapM_view_spec id (Retained initial)
    intro packet
    exact skb_retained (SkbStore.newTx packet) initial
  · change SameView SendWorkCauses.queue (packets.mapM newTxSkb)
    intro initial
    apply mapM_view_spec SendWorkCauses.queue (fun q => q = initial)
    intro packet
    exact (SendWorkCauses.skb_frame (SkbStore.newTx packet)).wp (fun q => q = initial)

theorem create (pid : PeerId) (items : List SkbId) : StateSafe (hooks.create pid items) := by
  apply observed_native _ _
    (RetirementSecurity.NestedPeerRelease.projects_erases old? (CausalJournal.create_projects pid items)
      (projected_erases _ _ Journal.nonce? (Journal.create_projects pid items)))
    (CallbackQuiet.create (fun _ : Event => (none : Option Empty))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items).1
  exact state_framed _ (createData_retained pid items) (SendWorkCauses.create_data_frame pid items)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
