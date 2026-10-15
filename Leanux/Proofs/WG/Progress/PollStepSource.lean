import Leanux.Proofs.WG.Progress.PollBoundModel
import Leanux.Proofs.WG.Roaming.PollEndpointSource
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Roaming Std.Do

theorem poll_any_normal {α : Type} (a : M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  rw [← ensures_iff]
  intro w x out pre run
  trivial

theorem pollCleanup_transition (pid : PeerId) (budget : Nat) (state : PollState)
    (id : SkbId) (pkt : RxPacket) (free : Bool) :
    Ensures (pollPacketCleanup pid budget state id pkt free) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  have hk := poll_any_normal (keypairPut (some pkt.keypair) false)
  have hp := poll_any_normal (peerPut (some pid))
  have hf := poll_any_normal (freeRxSkb id)
  rw [ensures_iff]
  mvcgen [pollPacketCleanup, branch, hk, hp, hf]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [PollTransition]

theorem pollSuffix_transition (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (state : PollState) (prepared : PollPrepared) :
    Ensures (pollEndpointSuffix pid budget toStack state prepared) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  cases prepared with
  | drained => intro w result out pre run; cases run; exact Or.inl ⟨rfl, rfl⟩
  | rejected id pkt => exact pollCleanup_transition pid budget state id pkt true
  | endpoint cut =>
    have hc := poll_any_normal (consumeDataAfterEndpoint pid cut.packet)
    have hg := fun gro inner => poll_any_normal (napiGroReceive toStack gro inner)
    have hp := fun gro => (ensures_iff _ _ _).mp
      (pollCleanup_transition pid budget (state.1, gro, state.2.2) cut.id cut.packet false)
    rw [ensures_iff]
    mvcgen [pollEndpointSuffix, hc, hg, hp]
    case inv1 => exact ((⇓? _ _ => ⌜True⌝) : PostCond _ (.arg World (.except Stop .pure)))
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [PollTransition]
    all_goals trivial

theorem pollStep_transition (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (turn : Nat) (state : PollState) :
    Ensures (pollStep pid budget toStack turn state) (fun _ => True)
      (fun result _ => PollTransition budget state result) := by
  rw [pollStep_endpoint_source]
  exact ensures_bind (pollEndpointPrefix pid) (pollEndpointSuffix pid budget toStack state)
    (Q := fun _ _ => True) (fun _ _ _ _ _ => True.intro)
    (fun prepared => pollSuffix_transition pid budget toStack state prepared)

end Leanux.Proofs.WG.Progress
