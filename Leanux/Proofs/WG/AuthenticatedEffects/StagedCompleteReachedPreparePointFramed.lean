import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCanonical

/-! Local access requirements follow actual successful bind prefixes. Focus
uses the original filtered history, and capture retains the same source body. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

variable {E F α β : Type} {action : WGPrefix E α}
variable {w v u : WGWorld} {a b c : Ambient} {h middle last : List E} {value : α}

def Framed : {E α : Type} → {action : WGPrefix E α} → Shape action → WGWorld → Ambient → List E → Prop
  | _,_,_,.pure _,_,_,_ => True
  | _,_,_,.quiet _ _,_,_,_ => True
  | _,_,_,.access token,w,_,_ => token.Entry w
  | _,_,_,@Shape.bind _ _ _ body _ head tail,w,a,h => Framed head w a h ∧
      ∀value v b middle,runWGPrefix body w a h=(.ok ((value,v),b),middle)→Framed (tail value) v b middle
  | _,_,_,.focus _ decode _ body,w,a,h => Framed body w a (h.filterMap decode)
  | _,_,_,.receipt body _,w,a,h => Framed body w a h

theorem Access.normal (token : Access action)
    (performed : runWGPrefix action w a h=(.ok ((value,v),b),last)) :
    (token.native.run w).run a=.ok ((value,v),b) ∧ last=h++token.events w value := by
  rw [token.run] at performed
  cases native : (token.native.run w).run a with
  | error reason => rw [native] at performed; cases performed
  | ok out =>
      obtain ⟨⟨result,next⟩,ambient⟩:=out
      rw [native] at performed
      cases performed
      exact ⟨rfl,rfl⟩

theorem Framed.normal {shape : Shape action} (framed : Framed shape w a h)
    (performed : runWGPrefix action w a h=(.ok ((value,v),b),last)) :
    StagedEntry.view v=StagedEntry.view w := by
  induction shape generalizing w a v b with
  | pure => cases performed; rfl
  | quiet body frame =>
      rw [runWGPrefix_lift] at performed
      exact (ProjectedAction.iff_run_ambient _ _ _).mp frame _ _ _ _ _ (congrArg Prod.fst performed)
  | access token => exact token.native_frame framed (token.normal performed).1
  | @bind E α β body next head tail ihHead ihTail =>
      change runStatePrefix _ w a h = _ at performed
      rw [runStatePrefix_bind] at performed
      cases front : runStatePrefix body w a h with
      | mk result history =>
          rw [front] at performed
          cases result with
          | error reason => cases performed
          | ok out =>
              obtain ⟨⟨x,next⟩,ambient⟩:=out
              exact (ihTail x (framed.2 x next ambient history front) performed).trans (ihHead framed.1 front)
  | focus encode decode inverse body ih =>
      have native := congrArg Prod.fst performed
      change (runWGPrefix _ w a (h.filterMap decode)).1=.ok ((value,v),b) at native
      exact ih framed (Prod.ext native rfl)
  | receipt body record ih =>
      rw [runWGPrefix_receiptWGObserved] at performed
      cases front : runWGPrefix _ w a h with
      | mk result history =>
          rw [front] at performed
          cases result with
          | error reason => cases performed
          | ok out =>
              obtain ⟨⟨x,next⟩,ambient⟩:=out
              cases performed
              exact ih framed front

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
