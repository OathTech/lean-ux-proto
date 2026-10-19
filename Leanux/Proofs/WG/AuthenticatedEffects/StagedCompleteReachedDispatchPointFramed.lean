import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointFrames

/-! Source frame certificates keep the stronger deletion input exactly at
that child. Every continuation requires its actual successful source prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

def Framed : {α : Type} → {action : PrefixM Event α} → Shape action → World → History → Prop
  | _,_,.pure _,w,h => CompleteProduct.Carrier h w
  | _,_,.native _,w,h => CompleteProduct.Carrier h w
  | _,_,.child child,w,h => child.Entry h w
  | _,_,@Shape.bind _ _ body _ head tail,w,h => Framed head w h ∧
      ∀value u middle,runPrefix body w h=(.ok (value,u),middle)→Framed (tail value) u middle
  | _,_,.marked _ body,w,h => Framed body w h

theorem Framed.carrier (framed : Framed shape w h) : CompleteProduct.Carrier h w := by
  induction shape with
  | pure => exact framed
  | native => exact framed
  | child token => exact token.entry_carrier framed
  | bind head tail ih _ => exact ih framed.1
  | marked _ body ih => exact ih framed

theorem Framed.normal {shape : Shape action} (framed : Framed shape w h)
    (performed : runPrefix action w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
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

def Family.Plain : Family → Prop
  | .delete => False
  | _ => True

def Plain : {α : Type} → {action : PrefixM Event α} → Shape action → Prop
  | _,_,.pure _ => True
  | _,_,.native _ => True
  | _,_,.child (.family source) => source.Plain
  | _,_,.bind head tail => Plain head ∧ ∀value,Plain (tail value)
  | _,_,.marked _ body => Plain body

theorem Family.plain_entry (source : Family) (plain : source.Plain) (before : CompleteProduct.Carrier h w) : source.Entry h w := by
  cases source <;> first | exact before | exact False.elim plain

theorem Plain.framed (plain : Plain shape) (before : CompleteProduct.Carrier h w) : Framed shape w h := by
  induction shape generalizing w h with
  | pure => exact before
  | native => exact before
  | child token => cases token with | family source => exact source.plain_entry plain before
  | bind head tail ihHead ihTail =>
    have framed := ihHead plain.1 before
    exact ⟨framed,fun value u middle run=>ihTail value (plain.2 value) (framed.normal run)⟩
  | marked label body ih => exact ih plain before

theorem Plain.source_mpr {left right : PrefixM Event α} (same : left=right)
    {shape : Shape right} (plain : Plain shape) : Plain ((congrArg Shape same).mpr shape) := by
  cases same; exact plain

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
