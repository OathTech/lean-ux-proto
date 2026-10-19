import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalLifetimeSource

/-! Exact projection of the nested completion repayment. The target is the
original lifetime observer, including all accesses before a stopped release. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.LifetimeSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects TransmitSecurity

private theorem state_focus_composed (e₁ : L → E) (d₁ : E → Option L)
    (e₂ : E → F) (d₂ : F → Option E) (action : WGPrefix L α) :
    focusStatePrefix e₂ d₂ (focusStatePrefix e₁ d₁ action) =
      focusStatePrefix (e₂ ∘ e₁) (fun e => (d₂ e).bind d₁) action := by
  funext w a h
  exact congrFun (congrFun (CompletionEffects.focus_composed e₁ d₁ e₂ d₂ (action.run w)) a) h

theorem put_target (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (peer : Option PeerId) :
    focusStatePrefix (peerEncode encode) (peerDecode decode) (Peers.peerPutPrefix peer) =
      (CompletionEffects.lifetimeBase encode decode).put peer := by
  simp only [CompletionEffects.lifetimeBase,LifetimeEffects.Ops.focus,LifetimeEffects.native,
    peerPutMixed,peerStateFocus,state_focus_composed]
  rfl

theorem put_projects (ρ : E → Option F)
    (eg : Completion.Event → E) (dg : E → Option Completion.Event)
    (et : Completion.Event → F) (dt : F → Option Completion.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt)
    (inverse : ∀ event, dt (et event) = some event)
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (putObserved eg dg record peer)
      ((CompletionEffects.lifetimeBase et dt).put peer) := by
  have encode : ∀ event, ρ (peerEncode eg event) = some (peerEncode et event) :=
    fun event => enc (CompletionEffects.lifetimeEvent (.peer event))
  have decode : ∀ event, peerDecode dg event = (ρ event).bind (peerDecode dt) := by
    intro event
    unfold peerDecode
    rw [dec]
    simp only [Option.bind_assoc]
  have project : PeerSource.Ops.Projects ρ
      (PeerSource.Ops.focus (peerEncode eg) (peerDecode dg) PeerSource.peers)
      (PeerSource.Ops.focus (peerEncode et) (peerDecode dt) PeerSource.peers) := by
    constructor
    all_goals intros
    all_goals exact CompletionEffects.state_focus_matching ρ _ _ _ _ encode decode _
  rw [← put_target]
  exact PeerSource.observed_focused_peers_projects ρ (peerEncode et) (peerDecode dt)
    (fun event => by simp [peerEncode,peerDecode,inverse,CompletionEffects.lifetimeEvent,
      CompletionEffects.lifetime?,Completion.disposition?,TxDisposition.accessEvent,LifetimeEvent.peer?])
    project record quiet peer

theorem decorate_projects (ρ : E → Option F)
    (eg : Completion.Event → E) (dg : E → Option Completion.Event)
    (et : Completion.Event → F) (dt : F → Option Completion.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt)
    (inverse : ∀ event, dt (et event) = some event)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (armQuiet : ∀ r, ρ (arm r) = none) (queueQuiet : ∀ r, ρ (queue r) = none)
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) :
    LifetimeEffects.Ops.Projects ρ (decorate eg dg scope arm queue record)
      (CompletionEffects.lifetimeBase et dt) :=
  {LifetimeEffects.decorate_projects ρ _ _
      (CompletionEffects.lifetimeBase_matching ρ eg dg et dt enc dec)
      scope arm queue armQuiet queueQuiet with
    put := put_projects ρ eg dg et dt enc dec inverse record quiet}

theorem fresh_target (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (inverse : ∀ event, decode (encode event) = some event) (pid : PeerId) :
    liftWGObserver (LifetimeEffects.freshWith (CompletionEffects.lifetimeBase encode decode) pid) =
      (CompletionEffects.focused encode decode).fresh pid := by
  rw [show CompletionEffects.lifetimeBase encode decode = LifetimeEffects.Ops.focus
    (encode ∘ CompletionEffects.lifetimeEvent)
    (fun e => (decode e).bind CompletionEffects.lifetime?) LifetimeEffects.native from rfl]
  rw [LifetimeEffects.fresh_focus _ _ (fun e => by
    simp [Function.comp_def,inverse,CompletionEffects.lifetimeEvent,CompletionEffects.lifetime?,
      Completion.disposition?,TxDisposition.accessEvent]) _ LifetimeEffects.native_appends]
  rw [CompletionEffects.lift_focus,← CompletionEffects.focus_composed]
  simp only [CompletionEffects.focused,CompletionEffects.native,CompletionEffects.access_factor,
    CompletionEffects.lift_focus,← LifetimeEffects.fresh_factor]

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.LifetimeSource
