import Leanux.Proofs.WG.Keypairs.Affiliation
import Leanux.Runner

/-! Initialization and native maintenance of nullable affiliation. All action
contracts concern normal endpoints of the actual WG and Ambient stack. -/
namespace Leanux.Proofs.WG.Affiliation
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Lifetimes

theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv w := by
  have hd := congrArg WGStoreView.dev hw
  change w.dev = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) at hd
  intro s hs
  by_cases active : (net && !bare) = true
  · simp only [view,hd,active,↓reduceIte,Option.map_some,Option.some.injEq] at hs
    subst s
    constructor <;> simp [state]
  · simp [view,hd,active] at hs

/-- Clearing any of the three possibly aliased key slots only drops references;
actual key releases may also erase their target cells. -/
theorem keypairsClear_affiliation (pid : PeerId) :
    Preserves Inv (keypairsClear pid) := by
  have get : Preserves Inv (getPeer pid) := by
    exact hoare_consequence (getPeer_spec (fun s => ∀ t, s = some t → t.Inv) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have modify (f : Peer → Peer)
      (stamp : ∀ p, (f p).internalId = p.internalId)
      (word : ∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
      (slots : ∀ p kid, (f p).keypairCurrent = some kid ∨
        (f p).keypairPrevious = some kid ∨ (f p).keypairNext = some kid →
        p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) :
      Preserves Inv ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
    apply hoare_consequence (modifyPeer_slots pid [] f stamp word
      (fun p kid h => (slots p kid h).elim Or.inl
        (fun h => h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))))
    · intro w hi s hs
      exact ⟨hi s hs, by simp⟩
    · intro _ w hi s hs
      exact (hi s hs).1
  have put (kp : Option KeypairId) : Preserves Inv (keypairPut kp true) := by
    exact keypairPut_affiliation (fun s => ∀ t, s = some t → t.Inv)
      (by intro s kid hi t ht; cases ht; exact (hi s rfl).eraseKey kid) kp true
  unfold keypairsClear
  apply preserves_bind get
  intro p
  apply preserves_bind (modify (fun p => {p with keypairNext := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases h))
  intro _
  apply preserves_bind (put p.keypairNext)
  intro _
  apply preserves_bind get
  intro p
  apply preserves_bind (modify (fun p => {p with keypairPrevious := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · exact Or.inl h
      · cases h
      · exact Or.inr (Or.inr h)))
  intro _
  apply preserves_bind (put p.keypairPrevious)
  intro _
  apply preserves_bind get
  intro p
  apply preserves_bind (modify (fun p => {p with keypairCurrent := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · cases h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)))
  intro _
  exact put p.keypairCurrent

theorem handshakeClear_view (pid : PeerId) : SameView view (handshakeClear pid) := by
  unfold handshakeClear
  apply SameView.bind (fun initial =>
    indexOwner_peerDeref_preserves (.handshake pid) (fun w => view w = initial))
  intro _
  apply SameView.bind (fun initial => hoare_liftIndex (indexRemove (.handshake pid))
    (fun w => view w = initial) (by
      intro g d table hi hd
      simpa only [view,hd,Option.map_some,state] using hi))
  intro _
  exact handshakeZero_view pid

theorem expireCurrentPeerKeypairs_view (pid : PeerId) :
    SameView view (expireCurrentPeerKeypairs pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      SameView view (StateT.lift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => view w = initial)
  have get : SameView view (getPeer pid) := by
    intro initial
    exact hoare_consequence (getPeer_spec (fun t => t = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  let invalidate (kp : KeypairId) : WG.M Unit := do
    let k ← getKeypair kp
    setKeypair kp {k with sending := {k.sending with isValid := false}}
  have invalidate_view (kp : KeypairId) : SameView view (invalidate kp) := by
    intro s
    unfold invalidate
    apply hoare_bind _ _ (getKeypair_spec (fun t => t = s) kp)
    intro k
    exact setKeypair_spec (fun t => t = s) kp _
  have reset : SameView view (resetLastSentHandshake pid) := by
    intro s
    unfold resetLastSentHandshake
    apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent)
      (fun w => view w = s))
    intro now
    apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
    intro p
    exact setPeer_spec (fun t => t = s) pid _
  let selected (decision : Decision) (slot : Option KeypairId) : WG.M Unit := do
    if ← branch decision slot.isSome then
      let some kp := slot | invariant "unreachable"
      invalidate kp
  have selected_view (decision : Decision) (slot : Option KeypairId) :
      SameView view (selected decision slot) := by
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
  apply SameView.bind reset
  intro _
  apply SameView.bind get
  intro p
  apply SameView.bind (selected_view .expireNextKeypair p.keypairNext)
  intro _
  exact selected_view .expireCurrentKeypair p.keypairCurrent

end Leanux.Proofs.WG.Affiliation
