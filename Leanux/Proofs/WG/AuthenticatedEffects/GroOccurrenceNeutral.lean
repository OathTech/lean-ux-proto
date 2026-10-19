import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollProjection

/-! Neutral occurrence metadata changes no callback, state, result, journal or
Stop. This is an equality of observers, not just native result erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem same (body : PrefixM E α) : ProjectsPrefix some id body body := by
  intro w h
  simp only [List.filterMap_some]
  cases runPrefix body w h with
  | mk result history => cases result <;> rfl

theorem eq_of_identity {body target : PrefixM E α}
    (projects : ProjectsPrefix some id body target) : body = target := by
  funext w h
  have equal := projects w h
  simp only [List.filterMap_some] at equal
  have identity : (runPrefix body w h).1.map (fun x => (id x.1, x.2)) =
      (runPrefix body w h).1 := by
    cases (runPrefix body w h).1 <;> rfl
  rw [identity] at equal
  exact equal.symm

theorem neutral
    (step : {α : Type} → WG.M α → PrefixM E α)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (callback : List (List UInt8) → PrefixM E Unit)
    (pid : PeerId) (budget : Nat) :
    sourceWith step enter leave counter consume
      (GroOccurrence.receiveWith liftPrefix (fun entries => callback (entries.map GroOccurrence.Entry.bytes)))
      (GroOccurrence.flushAllWith (fun entries => callback (entries.map GroOccurrence.Entry.bytes))) pid budget =
    CandidatePoll.sourceWith step enter leave counter consume
      (napiGroReceivePrefix callback) (napiGroFlushAllPrefix callback) pid budget := by
  apply eq_of_identity
  exact projects some id enter enter leave leave step step counter counter consume consume
    _ _ _ _ (fun _ _ => same _) (fun _ => same _) (fun _ => same _)
    (fun _ _ => same _) (fun _ _ _ => same _)
    (fun gro entry => GroOccurrence.receive_projects some _ callback (fun _ => same _) gro entry)
    (fun gro => GroOccurrence.flushAll_projects some _ callback (fun _ => same _) gro) pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
