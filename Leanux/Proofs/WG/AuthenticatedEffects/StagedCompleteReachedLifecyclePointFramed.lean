import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointFrames

/-! Source frame certificates keep the stronger deletion input exactly at
that child. Every continuation requires its actual successful source prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

def Framed : {α : Type} → {action : PrefixM Event α} → Shape action → World → History → Prop
  | _,_,.pure _,w,h => Account h w
  | _,_,.native token,w,h => token.Entry h w
  | _,_,.child child,w,h => child.Entry h w
  | _,_,@Shape.bind _ _ body _ head tail,w,h => Framed head w h ∧
      ∀value u middle,runPrefix body w h=(.ok (value,u),middle)→Framed (tail value) u middle
  | _,_,.marked _ body,w,h => Framed body w h

theorem Framed.account (framed : Framed shape w h) : Account h w := by
  induction shape with
  | pure => exact framed
  | native token => exact token.entry_account framed
  | child token => exact token.entry_account framed
  | bind head tail ih _ => exact ih framed.1
  | marked _ body ih => exact ih framed

theorem Framed.normal {shape : Shape action} (framed : Framed shape w h)
    (performed : runPrefix action w h=(.ok (value,v),last)) : Account last v := by
  induction shape generalizing w h last with
  | pure => cases performed; exact framed
  | native token => exact token.normal framed performed
  | child token => exact token.normal framed performed
  | bind head tail _ ih =>
    rw [runPrefix_bind] at performed
    cases front : runPrefix _ w h with
    | mk out middle =>
      rw [front] at performed
      cases out with
      | error reason => cases performed
      | ok pair => obtain ⟨value,u⟩ := pair; exact ih value (framed.2 value u middle front) performed
  | marked label body ih => exact ih framed performed

/-- Ordinary lifecycle fragments need no reset or creation phase fact. -/
def Ordinary : {α : Type} → {action : PrefixM Event α} → Shape action → Prop
  | _,_,.pure _ => True
  | _,_,.native (.quiet ..) => True
  | _,_,.native _ => False
  | _,_,.child (.family (.staging _)) => False
  | _,_,.child (.family (.keepalive _)) => False
  | _,_,.child _ => True
  | _,_,.bind head tail => Ordinary head ∧ ∀value,Ordinary (tail value)
  | _,_,.marked _ body => Ordinary body

theorem Ordinary.framed (ordinary : Ordinary shape) (before : Account h w) : Framed shape w h := by
  induction shape generalizing w h with
  | pure => exact before
  | native token => cases token <;> first | exact before | exact False.elim ordinary
  | child token => cases token with
    | family family => cases family <;> first | exact before | exact False.elim ordinary
  | bind head tail ihHead ihTail =>
    have framed := ihHead ordinary.1 before
    exact ⟨framed,fun value u middle run=>ihTail value (ordinary.2 value) (framed.normal run)⟩
  | marked label body ih => exact ih ordinary before

theorem Framed.source_mpr {left right : PrefixM Event α} (same : left=right)
    {shape : Shape right} (framed : Framed shape w h) :
    Framed ((congrArg Shape same).mpr shape) w h := by
  cases same
  exact framed

theorem Ordinary.source_mpr {left right : PrefixM Event α} (same : left=right)
    {shape : Shape right} (ordinary : Ordinary shape) :
    Ordinary ((congrArg Shape same).mpr shape) := by
  cases same
  exact ordinary

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
