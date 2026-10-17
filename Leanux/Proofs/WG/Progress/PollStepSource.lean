import Leanux.Proofs.WG.Progress.PollBoundModel
import Leanux.Proofs.WG.Roaming.PollEndpointSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Roaming Std.Do

theorem poll_any_normal {α : Type} (a : Leanux.M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  rw [← Noise.Product.ensures_iff]
  intro w x out pre run
  trivial

theorem pollCleanup_transition (pid : PeerId) (budget : Nat) (state : PollState)
    (id : SkbId) (pkt : RxPacket) (free : Bool) :
    Noise.Product.Ensures (pollPacketCleanup pid budget state id pkt free) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  have any {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
    intro w x out pre run
    trivial
  unfold pollPacketCleanup
  refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
  refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
  refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
  refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
  intro w result out pre run
  have ambientLift {α : Type} (a : AmbientM α) :
      (monadLift a : Leanux.M α) = liftAmbient a := rfl
  by_cases done : budget ≤ state.1 + 1
  all_goals simp [branch, ambientLift, AmbientM.branch, done] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, done, rfl⟩
  · exact ⟨rfl, by omega, rfl⟩

theorem pollSuffix_transition (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (state : PollState) (prepared : PollPrepared) :
    Noise.Product.Ensures (pollEndpointSuffix pid budget toStack state prepared) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  cases prepared with
  | drained => intro w result out pre run; cases run; exact Or.inl ⟨rfl, rfl⟩
  | rejected id pkt => exact pollCleanup_transition pid budget state id pkt true
  | endpoint cut =>
    have any {α : Type} (a : Leanux.M α) :
        Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
      intro w x out pre run
      trivial
    simp only [pollEndpointSuffix]
    refine Noise.Product.ensures_bind _ _ (any _) ?_
    intro inner
    cases inner with
    | none =>
      simpa using pollCleanup_transition pid budget state cut.id cut.packet false
    | some bytes =>
      simp only [Option.toList, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
      refine Noise.Product.ensures_bind _ _ (any _) ?_
      intro gro
      exact pollCleanup_transition pid budget (state.1, gro, state.2.2) cut.id cut.packet false

theorem pollStep_transition (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (turn : Nat) (state : PollState) :
    Noise.Product.Ensures (pollStep pid budget toStack turn state) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  rw [pollStep_endpoint_source]
  exact Noise.Product.ensures_bind (pollEndpointPrefix pid) (pollEndpointSuffix pid budget toStack state)
    (Q := fun _ _ => True) (fun _ _ _ _ _ => True.intro)
    (fun prepared => pollSuffix_transition pid budget toStack state prepared)

end Leanux.Proofs.WG.Progress
