import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuiet

/-! Complete actual take, restore, create and encryption callbacks are quiet
only for projections that ignore their stated receipt constructors. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {F : Type}

theorem selection (ρ : Event → Option F)
    (taken : ∀ r, ρ (.stagingTaken r) = none)
    (selected : ∀ pid r, ρ (.old (.responder (.selected pid r))) = none) (pid : PeerId) :
    StateQuiet ρ (CausalJournal.selection pid) := by
  apply state_of_history
  intro before
  unfold CausalJournal.selection Take.selection Take.observed
  apply CallbackHistory.state_receipt _ _ _ (fun r => state_history (state_emit ρ _ (selected pid r)) before)
  exact Driver.History.state_bind
    (CallbackHistory.state_receipt _ (Driver.History.state_lift _) _
      (fun r => state_history (state_emit ρ _ (taken _)) before))
    (fun _ => Driver.History.state_lift _)

theorem restore (ρ : Event → Option F) (restored : ∀ r, ρ (.stagedRestored r) = none)
    (pid : PeerId) (packets : List Packet) : StateQuiet ρ (CausalJournal.stagedRestore pid packets) := by
  apply state_of_history
  intro before
  exact CallbackHistory.state_receipt _ (Driver.History.state_lift _) _
    (fun r => state_history (state_emit ρ _ (restored _)) before)

private theorem publish_history (ρ : Event → Option F) (old : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none) (before : List F)
    (item : List SkbId) (state : PacketState) :
    Driver.ProductHistorySafe (fun events => events.filterMap ρ = before)
      (TxSource.publish (TxSource.observed txEvent txEvent? Event.stagedDisposal) item state) := by
  unfold TxSource.publish
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head TxSource.releaseObserved; exact product_history (release ρ old disposal _) before)
    | (driver_history_head focusPrefix; exact product_history (product_focus ρ txEvent txEvent? old _) before)
    | driver_product_history_step

theorem create (ρ : Event → Option F) (old : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (terminal : ∀ e, ρ (.terminalDrop e) = none) (pid : PeerId) (item : List SkbId) :
    StateQuiet ρ (CausalJournal.create pid item) := by
  apply lower
  apply product_of_history
  intro before
  unfold Terminal.createObserved Terminal.createWith Terminal.freeObserved Terminal.observed
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head TxSource.releaseObserved; exact product_history (release ρ old disposal _) before)
    | (driver_history_head TxSource.publish; exact publish_history ρ old disposal before _ _)
    | (driver_history_head receiptObserved; refine CallbackHistory.product_receipt _ ?_ _
        (fun r => product_history (product_emit ρ _ (terminal _)) before))
    | (driver_history_head focusPrefix; exact product_history (product_focus ρ txEvent txEvent? old _) before)
    | driver_product_history_step

theorem publication (ρ : Event → Option F) (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (item : List SkbId) (state : PacketState) :
    StateQuiet ρ (Publication.observed Event.stagedDisposal stagedDisposal? item state) := by
  have quiet (peer : Option PeerId) : StateQuiet ρ
      (Decoration.release Event.stagedDisposal stagedDisposal? peer) :=
    state_focus ρ Event.stagedDisposal stagedDisposal? disposal _
  exact ⟨Publication.appends _ (fun p => (quiet p).1) item state,
    Publication.frame _ (fun p => (quiet p).2) item state⟩

private theorem encryption_after (ρ : Event → Option F)
    (encrypted : ∀ r, ρ (.old (.encrypted r)) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none) (before : List F)
    (item : List SkbId) (skb : SkbId) (head : RunWitness DataPacket) :
    Driver.ProductHistorySafe (fun events => events.filterMap ρ = before)
      (EncryptionSource.afterHead
        (EncryptionSource.observed (Event.old ∘ Journal.Event.encrypted)
          (fun event => (old? event).bind Journal.encryption?) Event.stagedDisposal stagedDisposal?)
        item skb head) := by
  unfold EncryptionSource.afterHead
  simp only [EncryptionSource.observed,EncryptionSource.focused]
  repeat' first
    | (driver_history_head Publication.observed;
        exact product_history (state_product (publication ρ disposal _ _)) before)
    | (driver_history_head focusPrefix; exact product_history (product_focus ρ _ _ encrypted _) before)
    | driver_product_history_step

theorem encrypt (ρ : Event → Option F)
    (encrypted : ∀ r, ρ (.old (.encrypted r)) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (returned : ∀ item r, ρ (.old (.encryptionReturn item r)) = none)
    (item : Option (List SkbId)) : ProductQuiet ρ (CausalJournal.encrypt item) := by
  apply product_of_history
  intro before
  unfold CausalJournal.encrypt
  apply CallbackHistory.product_receipt _ _ _
    (fun r => product_history (product_emit ρ _ (returned item r)) before)
  unfold EncryptionSource.tail
  simp only [EncryptionSource.observed,EncryptionSource.focused]
  repeat' first
    | (driver_history_head EncryptionSource.afterHead; exact encryption_after ρ encrypted disposal before _ _ _)
    | (driver_history_head focusPrefix; exact product_history (product_focus ρ _ _ encrypted _) before)
    | driver_product_history_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
