import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedHistory

/-! Exact callback append/frame contracts. These preserve an independently
chosen event projection through the actual nested releases, not by native
erasure. The projection must explicitly ignore each newly recorded event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

abbrev StateQuiet (ρ : Event → Option F) (body : WGPrefix Event α) :=
  StateAppends body ∧ StateHistoryFrame ρ body
abbrev ProductQuiet (ρ : Event → Option F) (body : PrefixM Event α) :=
  Appends body ∧ HistoryFrame ρ body

variable {F : Type} {ρ : Event → Option F}

theorem state_history (h : StateQuiet ρ body) (before : List F) :
    Driver.StateHistorySafe (fun events => events.filterMap ρ = before) body := by
  intro w a events ready
  obtain ⟨suffix,grown⟩ := h.1 w a events
  have kept := (h.2 w a events).trans ready
  refine ⟨suffix,grown,kept,?_⟩
  cases (runPrefix (body.run w) a events).1 <;> trivial

theorem product_history (h : ProductQuiet ρ body) (before : List F) :
    Driver.ProductHistorySafe (fun events => events.filterMap ρ = before) body := by
  intro w events ready
  obtain ⟨suffix,grown⟩ := h.1 w events
  have kept := (h.2 w events).trans ready
  refine ⟨suffix,grown,kept,?_⟩
  cases (runPrefix body w events).1 <;> trivial

theorem state_of_history (h : ∀ before : List F,
    Driver.StateHistorySafe (fun events => events.filterMap ρ = before) body) : StateQuiet ρ body := by
  constructor
  · intro w a events
    obtain ⟨suffix,grown,_,_⟩ := h (events.filterMap ρ) w a events rfl
    exact ⟨suffix,grown⟩
  · intro w a events
    obtain ⟨_,_,kept,_⟩ := h (events.filterMap ρ) w a events rfl
    exact kept

theorem product_of_history (h : ∀ before : List F,
    Driver.ProductHistorySafe (fun events => events.filterMap ρ = before) body) : ProductQuiet ρ body := by
  constructor
  · intro w events
    obtain ⟨suffix,grown,_,_⟩ := h (events.filterMap ρ) w events rfl
    exact ⟨suffix,grown⟩
  · intro w events
    obtain ⟨_,_,kept,_⟩ := h (events.filterMap ρ) w events rfl
    exact kept

theorem state_focus (ρ : Event → Option F) (encode : G → Event) (decode : Event → Option G)
    (quiet : ∀ e, ρ (encode e) = none) (body : WGPrefix G α) :
    StateQuiet ρ (focusStatePrefix encode decode body) :=
  ⟨StateAppends.focus _ _ _,fun w => focusPrefix_other encode decode ρ quiet (body.run w)⟩

theorem product_focus (ρ : Event → Option F) (encode : G → Event) (decode : Event → Option G)
    (quiet : ∀ e, ρ (encode e) = none) (body : PrefixM G α) :
    ProductQuiet ρ (focusPrefix encode decode body) :=
  ⟨Appends.focus _ _ _,focusPrefix_other encode decode ρ quiet body⟩

theorem state_emit (ρ : Event → Option F) (event : Event) (quiet : ρ event = none) :
    StateQuiet ρ (emitStatePrefix event) :=
  ⟨fun _ _ _ => ⟨[event],rfl⟩,fun _ => HistoryFrame.emit event quiet⟩

theorem product_emit (ρ : Event → Option F) (event : Event) (quiet : ρ event = none) :
    ProductQuiet ρ (emitPrefix event) :=
  ⟨fun _ _ => ⟨[event],rfl⟩,HistoryFrame.emit event quiet⟩

theorem state_product (h : StateQuiet ρ body) : ProductQuiet ρ (liftWGObserver body) :=
  ⟨h.1.liftWGObserver,h.2.liftWGObserver⟩

theorem lower (h : ProductQuiet ρ body) : StateQuiet ρ (NativeAdapter.lower body) :=
  ⟨fun w a events => h.1 (NativeAdapter.world w a) events,
    fun w a events => h.2 (NativeAdapter.world w a) events⟩

theorem peer (ρ : Event → Option F) (encode : Peers.PeerEvent → Event)
    (decode : Event → Option Peers.PeerEvent) (old : ∀ e, ρ (encode e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none) (pid : Option PeerId) :
    StateQuiet ρ (PeerSource.observed
      (PeerSource.Ops.focus encode decode PeerSource.peers) Event.stagedDisposal pid) := by
  apply state_of_history
  intro before
  exact CallbackHistory.peer encode decode
    (fun body => state_history (state_focus ρ encode decode old body) before)
    (fun e => state_history (state_emit ρ _ (disposal e)) before) pid

theorem release (ρ : Event → Option F) (old : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none) (pid : Option PeerId) :
    ProductQuiet ρ (TxSource.releaseObserved txEvent txEvent? Event.stagedDisposal pid) :=
  state_product (peer ρ _ _ (fun e => old (.access (.peer e))) disposal pid)

theorem dispose (ρ : Event → Option F) (old : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none) (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProductQuiet ρ (TxSource.dispose (TxSource.observed txEvent txEvent? Event.stagedDisposal) pid item key) := by
  apply product_of_history
  intro before
  exact CallbackHistory.tx_dispose
    (fun body => product_history (product_focus ρ txEvent txEvent? old body) before)
    (fun p => product_history (release ρ old disposal p) before) pid item key

theorem dead (ρ : Event → Option F) (old : ∀ e, ρ (txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (terminal : ∀ e, ρ (.terminalDrop e) = none)
    (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    ProductQuiet ρ (Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item head) := by
  apply product_of_history
  intro before
  exact CallbackHistory.dead
    (fun body => product_history (product_focus ρ txEvent txEvent? old body) before)
    (fun p => product_history (release ρ old disposal p) before)
    (fun r => product_history (product_emit ρ _ (terminal r)) before) pid item head

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackQuiet
