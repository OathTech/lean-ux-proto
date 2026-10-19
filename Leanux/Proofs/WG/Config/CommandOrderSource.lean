import Leanux.Proofs.WG.Config.CommandOrderEffects
import Leanux.Proofs.WG.Config.AllowedOrderSource
import Leanux.Proofs.WG.Queues.JointPeerCommand

/-! Composition over the unchanged C1 peer-command observer and acquisition factories. Quiet validation, lookup, creation and reference actions retain the routing journal; actual update branches use the existing AllowedOrder contract. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do
open AllowedOrder

theorem and_factor (first second : Decision) (x y : Bool) :
    (liftWGPrefix (WG.andM (branch first x) (branch second y)) :
      WGPrefix RoutingCompletion Bool) =
    (do mark first x
        if x then mark second y
        pure (x && y)) := by
  cases x <;> rfl


theorem out_spec (attrs : PeerAttrs) (requested : UInt32) (ret : Int)
    (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Segment (Partial attrs requested) before)
      (peerConfigOutObserved attrs none ret)
      (fun value=>Segment (fun events=>Finished attrs requested events value) before) := by
  have safe : ∀h,h=before→Segment (Partial attrs requested) before h := by
    intro h same
    subst h
    exact empty_segment (partial_empty attrs requested) before
  exact (AllowedOrder.out_rule attrs none ret (fun h=>h=before) _ safe).consequence
    (fun _ _ _ h=>h) (fun value h _ _ point=>by
      obtain ⟨_,same⟩:=point
      subst h
      exact empty_segment (finished_empty attrs requested value) before)

theorem update_spec (attrs : PeerAttrs) (requested effective : UInt32)
    (flags : EffectiveFlags requested effective) (psk : Option Key) (pid : PeerId)
    (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Segment (Partial attrs requested) before)
      (peerConfigUpdateObserved attrs (some pid) effective psk pid)
      (fun value=>Segment (fun events=>Finished attrs requested events value) before) := by

  intro w a h initial
  obtain ⟨suffix,hs,safe,post⟩ :=
    AllowedOrder.update_spec attrs (some pid) effective psk pid before w a h initial
  refine ⟨suffix,hs,?_,?_⟩
  · obtain ⟨events,same,shape⟩:=safe
    exact ⟨events,same,Or.inr ⟨pid,effective,flags,shape⟩⟩
  · cases output : (runPrefix
      (StateT.run (peerConfigUpdateObserved attrs (some pid) effective psk pid) w) a h).1 with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      simp only [output] at post ⊢
      obtain ⟨events,same,shape⟩:=post
      exact ⟨events,same,Or.inr ⟨pid,effective,flags,shape⟩⟩

theorem acquired_spec (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (requested : UInt32) (peer : Option PeerId) (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before) (Segment (Partial attrs requested) before)
      (peerCommandAcquiredWith (fun {_} a=>liftWGPrefix a)
        (fun k p=>liftWGPrefix (peerCreate k p)) (fun pid=>liftWGPrefix (peerGet pid))
        (peerConfigOutObserved attrs none) (peerConfigUpdateObserved attrs)
        key psk requested peer)
      (fun value=>Segment (fun events=>Finished attrs requested events value) before) := by
  have safe : ∀h,h=before→Segment (Partial attrs requested) before h := by
    intro h same
    subst h
    exact empty_segment (partial_empty attrs requested) before

  unfold peerCommandAcquiredWith
  cases peer with
  | none =>
    simp only [Option.isNone_none,branch_factor,and_factor,
      bind_assoc,pure_bind,ite_true]
    apply mark_then _ _ safe
    apply mark_then _ _ safe
    split
    · exact out_spec attrs requested _ before
    · apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
      intro d
      apply mark_then _ _ safe
      by_cases identity : d.staticIdentity.hasIdentity=true
      · simp only [identity,ite_true]
        apply mark_then _ _ safe
        split
        · exact out_spec attrs requested _ before
        · apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
          intro result
          cases result with
          | error err =>
            apply mark_then _ _ safe
            exact out_spec attrs requested _ before
          | ok pid =>
            apply mark_then _ _ safe
            apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
            intro _
            exact update_spec attrs requested _ (Or.inr rfl) psk pid before
      · simp only [identity,Bool.false_eq_true,ite_false,Bool.false_and,pure_bind]
        apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
        intro result
        cases result with
        | error err =>
          apply mark_then _ _ safe
          exact out_spec attrs requested _ before
        | ok pid =>
          apply mark_then _ _ safe
          apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
          intro _
          exact update_spec attrs requested _ (Or.inr rfl) psk pid before
  | some pid =>
    simp only [Option.isNone_some,branch_factor,bind_assoc,pure_bind,
      Bool.false_eq_true,ite_false]
    apply mark_then _ _ safe
    exact update_spec attrs requested requested (Or.inl rfl) psk pid before

theorem command_spec (attrs : PeerAttrs) (before : List RoutingCompletion) :
    HistorySpec (fun h=>h=before)
      (Segment (Partial attrs (attrs.flags.getD 0)) before)
      (setPeerCmdObserved attrs)
      (fun value=>Segment (fun events=>Finished attrs (attrs.flags.getD 0) events value) before) := by
  have safe : ∀h,h=before→Segment (Partial attrs (attrs.flags.getD 0)) before h := by
    intro h same
    subst h
    exact empty_segment (partial_empty attrs _) before
  rw [setPeerCmdObserved_factor]
  unfold setPeerCmdWith
  cases pk : attrs.publicKey <;> cases psk : attrs.presharedKey <;> cases flags : attrs.flags <;>
    simp only [flags,Option.isSome_none,Option.isSome_some,Option.getD_none,
      Option.getD_some,and_factor,branch_factor,bind_assoc,pure_bind,
      Bool.false_eq_true,ite_false,ite_true,Bool.true_and,Bool.false_and,
      Bool.not_true,Bool.not_false] at safe ⊢
  all_goals
    repeat' first
      | (maintenance_head peerConfigOutObserved
         exact out_spec attrs _ _ before)
      | (maintenance_head peerCommandAcquiredWith
         exact acquired_spec attrs _ _ _ _ before)
      | with_reducible apply mark_then _ _ safe
      | with_reducible apply StatePrefixEnsures.bind (quiet _ (fun h=>h=before) _ safe)
      | (maintenance_intro; try dsimp only)
      | split

end Leanux.Proofs.WG.Config.CommandOrder
