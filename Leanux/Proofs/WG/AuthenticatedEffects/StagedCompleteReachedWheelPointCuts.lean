import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointExecution

/-! Points select only native boundaries of the canonical shape. Each right
point contains the original successful left run; remainders are built from
those same binds, including the validation after installation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open TransmitSecurity.Staged.Obligations
variable {pid : PeerId} {saved : Peer}

inductive Site where
  | entry
  | returned
  | reading
  | left (site : Site)
  | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} →
    Shape pid saved action → World → History → Site → World → History → Prop where
  | entry (shape : Shape pid saved action) : Point shape w h .entry w h
  | returned (shape : Shape pid saved action)
      (run : runPrefix action w h = (.ok (value,u),middle)) : Point shape w h .returned u middle
  | reading {w : World} {id : PeerId} (point : ReadAccess.Point (ReadAccess.peerShape id) w.wg w.ambient v b) :
      Point (.native (.peer id)) w h .reading {w with wg:=v,ambient:=b} h
  | left {action : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape pid saved action}
      (tail : ∀ value, Shape pid saved (next value)) (point : Point head w h site u middle) :
      Point (.bind head tail) w h (.left site) u middle
  | right {action : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape pid saved action) (tail : ∀ value, Shape pid saved (next value))
      (leading : runPrefix action w h = (.ok (value,u),middle))
      (point : Point (tail value) u middle site v last) : Point (.bind head tail) w h (.right site) v last

theorem Point.frame {shape : Shape pid saved action} (point : Point shape w h site u middle)
    (cache : Cache pid saved w.wg) :
    middle = h ∧ StagedEntry.view u.wg = StagedEntry.view w.wg ∧ Cache pid saved u.wg := by
  induction point with
  | entry shape => exact ⟨rfl,rfl,cache⟩
  | reading point => exact ⟨rfl,point.frame,by rw [point.world];exact cache⟩
  | returned shape run => exact shape.normal cache run
  | left tail point ih => exact ih cache
  | right head tail leading point ih =>
    have first := head.normal cache leading
    have second := ih first.2.2
    exact ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2⟩

theorem Point.accounted {shape : Shape pid saved action} (point : Point shape w h site u middle)
    (cache : Cache pid saved w.wg) (before : CompleteCarrier.Accounted h ledger debts locals w.wg) :
    CompleteCarrier.Accounted middle ledger debts locals u.wg := by
  have same := point.frame cache
  rw [same.1]
  exact before.same_view same.2.1

inductive Residual : {α : Type} → {action : PrefixM Event α} → Shape pid saved action →
    World → History → Site → World → History → PrefixM Event α → Prop where
  | entry (shape : Shape pid saved action) : Residual shape w h .entry w h action
  | returned (shape : Shape pid saved action)
      (run : runPrefix action w h = (.ok (value,u),middle)) : Residual shape w h .returned u middle (pure value)
  | reading {w : World} {id : PeerId} (point : ReadAccess.Point (ReadAccess.peerShape id) w.wg w.ambient v b) :
      Residual (.native (.peer id)) w h .reading {w with wg:=v,ambient:=b} h (readRemainder h point)
  | left {action : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape pid saved action}
      (tail : ∀ value, Shape pid saved (next value))
      (remaining : Residual head w h site u middle remainder) :
      Residual (.bind head tail) w h (.left site) u middle (remainder >>= next)
  | right {action : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape pid saved action) (tail : ∀ value, Shape pid saved (next value))
      (leading : runPrefix action w h = (.ok (value,u),middle))
      (remaining : Residual (tail value) u middle site v last remainder) :
      Residual (.bind head tail) w h (.right site) v last remainder

theorem Residual.run {shape : Shape pid saved action} (cut : Residual shape w h site u middle remainder) :
    runPrefix action w h = runPrefix remainder u middle := by
  induction cut with
  | entry shape => rfl
  | reading point => exact readRemainder_run _ point
  | returned shape performed => rw [performed,runPrefix_pure]
  | left tail remaining ih => rw [runPrefix_bind,runPrefix_bind,ih]
  | right head tail leading remaining ih => rw [runPrefix_bind,leading]; exact ih

theorem Point.residual {shape : Shape pid saved action} (point : Point shape w h site u middle) :
    ∃ remaining, Residual shape w h site u middle remaining := by
  induction point with
  | entry shape => exact ⟨_,.entry shape⟩
  | reading point => exact ⟨_,.reading point⟩
  | returned shape performed => exact ⟨_,.returned shape performed⟩
  | left tail point ih => obtain ⟨remaining,source⟩ := ih; exact ⟨_,.left tail source⟩
  | right head tail leading point ih => obtain ⟨remaining,source⟩ := ih; exact ⟨_,.right head tail leading source⟩

theorem Residual.point {shape : Shape pid saved action} (cut : Residual shape w h site u middle remainder) :
    Point shape w h site u middle := by
  induction cut with
  | entry shape => exact .entry shape
  | reading point => exact .reading point
  | returned shape performed => exact .returned shape performed
  | left tail source ih => exact .left tail ih
  | right head tail leading source ih => exact .right head tail leading ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
