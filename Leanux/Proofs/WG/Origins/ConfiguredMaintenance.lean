import Leanux.Proofs.WG.Origins.ConfiguredSession
import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Runner

/-! Initialization and native maintenance for the existing configured registry
and session-support predicates. These are partial endpoint contracts. A Stop
has no invented final WG state, and the ambient input remains unrestricted. -/
namespace Leanux.Proofs.WG.ConfiguredMaintenance
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Lifetimes

/-- Only the original seven WG store fields are fixed at initialization. -/
theorem configured_initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    ConfiguredIdentity.Inv w := by
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) at hd
  intro s hs
  by_cases active : (net && !bare) = true
  · simp only [ConfiguredIdentity.view,hd,active,↓reduceIte,Option.map_some,Option.some.injEq] at hs
    subst s
    constructor <;> simp [ConfiguredIdentity.state]
  · simp [ConfiguredIdentity.view,hd,active] at hs

/-- The absent device and empty fixture key store need no historical receipt. -/
theorem session_initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    ConfiguredSession.Inv [] w := by
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) at hd
  intro d hdev id key hk valid
  by_cases active : (net && !bare) = true
  · simp only [hd,active,↓reduceIte,Option.some.injEq] at hdev
    subst d
    simp at hk
  · simp [hd,active] at hdev

/-- Clearing key slots retains the full configured peer cell, including its
allocation stamp and static key; key release follows the actual native source. -/
theorem keypairsClear_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (keypairsClear pid) := by
  have get : SameView ConfiguredIdentity.view (getPeer pid) := by
    intro initial
    exact hoare_consequence (ConfiguredIdentity.getPeer_spec (fun t => t = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  unfold keypairsClear
  apply SameView.bind get
  intro p
  apply SameView.bind (ConfiguredIdentity.modifyPeer_view pid
    (fun p => {p with keypairNext := none}) (fun _ => rfl))
  intro _
  apply SameView.bind (ConfiguredIdentity.keypairPut_view p.keypairNext true)
  intro _
  apply SameView.bind get
  intro p
  apply SameView.bind (ConfiguredIdentity.modifyPeer_view pid
    (fun p => {p with keypairPrevious := none}) (fun _ => rfl))
  intro _
  apply SameView.bind (ConfiguredIdentity.keypairPut_view p.keypairPrevious true)
  intro _
  apply SameView.bind get
  intro p
  apply SameView.bind (ConfiguredIdentity.modifyPeer_view pid
    (fun p => {p with keypairCurrent := none}) (fun _ => rfl))
  intro _
  exact ConfiguredIdentity.keypairPut_view p.keypairCurrent true

theorem handshakeClear_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (handshakeClear pid) := by
  unfold handshakeClear
  apply SameView.bind (fun initial =>
    indexOwner_peerDeref_preserves (.handshake pid) (fun w => ConfiguredIdentity.view w = initial))
  intro _
  apply SameView.bind (fun initial => hoare_liftIndex (indexRemove (.handshake pid))
    (fun w => ConfiguredIdentity.view w = initial) (by
      intro g d table hi hd
      simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi))
  intro _
  exact ConfiguredIdentity.handshakeZero_view pid

theorem expireCurrentPeerKeypairs_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (expireCurrentPeerKeypairs pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      SameView ConfiguredIdentity.view (StateT.lift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => ConfiguredIdentity.view w = initial)
  have get : SameView ConfiguredIdentity.view (getPeer pid) := by
    intro initial
    exact hoare_consequence (ConfiguredIdentity.getPeer_spec (fun t => t = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  let invalidate (kp : KeypairId) : WG.M Unit := do
    let k ← getKeypair kp
    setKeypair kp {k with sending := {k.sending with isValid := false}}
  have invalidate_view (kp : KeypairId) : SameView ConfiguredIdentity.view (invalidate kp) := by
    apply SameView.bind (ConfiguredIdentity.getKeypair_view kp)
    intro k
    exact ConfiguredIdentity.setKeypair_view kp _
  let selected (decision : Decision) (slot : Option KeypairId) : WG.M Unit := do
    if ← branch decision slot.isSome then
      let some kp := slot | invariant "unreachable"
      invalidate kp
  have selected_view (decision : Decision) (slot : Option KeypairId) :
      SameView ConfiguredIdentity.view (selected decision slot) := by
    unfold selected
    apply SameView.bind (ambient (AmbientM.branch decision slot.isSome))
    intro present
    cases present with
    | false => exact SameView.pure _ _
    | true =>
      cases slot with
      | none => exact ambient (AmbientM.invariant "unreachable")
      | some kp => exact invalidate_view kp
  have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
      (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
    congrArg (fun k => a >>= k) (funext h)
  have factor : expireCurrentPeerKeypairs pid = (do
      requireNotPending pid "clearing the handshake"
      handshakeClear pid
      resetLastSentHandshake pid
      let p ← getPeer pid
      selected .expireNextKeypair p.keypairNext
      selected .expireCurrentKeypair p.keypairCurrent) := by
    simp only [expireCurrentPeerKeypairs,selected,invalidate,requireNotPending,pure_bind]
    apply bind_congr
    intro _
    apply bind_congr
    intro _
    apply bind_congr
    intro p
    simp only [bind_assoc]
    apply bind_congr
    intro present
    cases present <;> cases p.keypairNext <;> cases p.keypairCurrent
    all_goals dsimp only
    all_goals try simp only [↓reduceIte]
    all_goals first | rfl | (symm; exact bind_assoc _ _ _) | (rw [pure_bind]; rfl)
  rw [factor]
  simp only [requireNotPending,pure_bind]
  apply SameView.bind (handshakeClear_view pid)
  intro _
  apply SameView.bind (ConfiguredIdentity.resetHandshake pid)
  intro _
  apply SameView.bind get
  intro p
  apply SameView.bind (selected_view .expireNextKeypair p.keypairNext)
  intro _
  exact selected_view .expireCurrentKeypair p.keypairCurrent

theorem beginSession_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (beginSession pid) := by
  rw [SessionOrigin.factor]
  apply SameView.bind (ConfiguredSession.front_view pid)
  intro front
  cases front with
  | none => exact SameView.pure _ _
  | some ctx => exact ConfiguredSession.tail_view pid ctx.slot

/-- The actual native endpoint preserves both existing predicates when its
configured cells are unchanged and receiving material is retained. -/
theorem preserves {α : Type} (a : WG.M α)
    (identity : SameView ConfiguredIdentity.view a)
    (material : Origins.Retaining.RetainsCall a) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ ConfiguredSession.Inv history w) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hv := (ProjectedAction.iff_run_ambient _ _ _).mp identity w ambient result v ambient' hr
  constructor
  · intro s hs
    exact hi.1 s (hv.symm.trans hs)
  · exact hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp material
      w ambient result v ambient' hr)

theorem keypairsClear_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ ConfiguredSession.Inv history w)
      (keypairsClear pid) :=
  preserves _ (keypairsClear_view pid) (Origins.Retaining.keypairsClear_material pid) history

theorem handshakeClear_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ ConfiguredSession.Inv history w)
      (handshakeClear pid) :=
  preserves _ (handshakeClear_view pid)
    (Origins.Retaining.of_view (Origins.Retaining.handshakeClear_material pid)) history

theorem expireCurrentPeerKeypairs_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ ConfiguredSession.Inv history w)
      (expireCurrentPeerKeypairs pid) :=
  preserves _ (expireCurrentPeerKeypairs_view pid)
    (Origins.Retaining.expireCurrentPeerKeypairs_material pid) history

/-- Normal completion keeps the configured registry and appends the actual
front receipt with its own WG and ambient endpoints. This gives no endpoint
assertion for a failed tail and no current-owner stamp conclusion. -/
theorem beginSession_preserves (pid : PeerId) (w v : WGWorld) (result : Bool)
    (ambient ambient' : Ambient) (history : List SessionOrigin.Receipt)
    (configured : ConfiguredIdentity.Inv w) (supported : ConfiguredSession.Inv history w)
    (hr : ((beginSession pid).run w).run ambient = .ok ((result,v),ambient')) :
    ConfiguredIdentity.Inv v ∧
      ∃ front u middle, ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) ∧
        ConfiguredSession.Inv
          (history ++ [SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]) v := by
  constructor
  · have hv := (ProjectedAction.iff_run_ambient _ _ _).mp (beginSession_view pid)
      w ambient result v ambient' hr
    intro s hs
    exact configured s (hv.symm.trans hs)
  · exact ConfiguredSession.beginSession_support pid w v result ambient ambient'
      history configured supported hr

end Leanux.Proofs.WG.ConfiguredMaintenance
