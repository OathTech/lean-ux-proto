import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointFrames

/-! Child completeness remains explicit. Points use the canonical source
shape and actual successful left operands; no factor equation constructs a
point or a native state for an error. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev ChildPoints := (α : Type) → (action : PrefixM Event α) → Child action →
  World → History → World → History → Prop

inductive Site where
  | entry
  | returned
  | interior
  | left (site : Site)
  | right (site : Site)
  | marked (label : Label) (site : Site)

inductive Point (inside : ChildPoints) : {α : Type} → {action : PrefixOuter Event α} →
    Shape action → History → Site → World → History → Prop where
  | nativeEntry (token : Native action) : Point inside (.native token) h .entry token.input h
  | nativeReturn (token : Native action) (performed : runPrefixOuter action h=(.ok out,last)) :
      Point inside (.native token) h .returned (token.output out) last
  | childEntry (token : Child action) : Point inside (.child index w token) h .entry w h
  | childReturn (token : Child action)
      (performed : runPrefixOuter (runAtPrefix index w action) h=(.ok out,last)) :
      Point inside (.child index w token) h .returned out.2 last
  | interior (token : Child action) (point : inside _ _ token w h u middle) :
      Point inside (.child index w token) h .interior u middle
  | left {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
      {head : Shape body} (tail : ∀ value,Shape (next value))
      (point : Point inside head h site u middle) : Point inside (.bind head tail) h (.left site) u middle
  | right {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefixOuter body h=(.ok value,middle))
      (point : Point inside (tail value) middle site u last) :
      Point inside (.bind head tail) h (.right site) u last
  | snapshot (label : Label) (w : World) (body : Shape action) :
      Point inside (.marked label w body) h (.marked label .entry) w h
  | marked (label : Label) (w : World) (point : Point inside shape h site u middle) :
      Point inside (.marked label w shape) h (.marked label site) u middle

/-- The source-local certificate has actual normal prefixes as its bind
premises. Canonical initialized construction, rather than an endpoint history
existential, must discharge this certificate. -/
def Framed : {α : Type} → {action : PrefixOuter Event α} → Shape action → History → Prop
  | _,_,.pure _,_ => True
  | _,_,.stopped _,_ => True
  | _,_,.native token,h => CompleteProduct.Carrier h token.input
  | _,_,.child _ w token,h => token.Entry h w
  | _,_,@Shape.bind _ _ body _ head tail,h => Framed head h ∧
      ∀value middle,runPrefixOuter body h=(.ok value,middle)→Framed (tail value) middle
  | _,_,.marked _ w body,h => CompleteProduct.Carrier h w ∧ Framed body h

theorem Framed.pure (value : α) : Framed (.pure value) h := True.intro
theorem Framed.stopped (reason) : Framed (.stopped (α:=α) reason) h := True.intro
theorem Framed.native (token : Native action) (before : CompleteProduct.Carrier h token.input) :
    Framed (.native token) h := before
theorem Framed.child (token : Child action) (before : token.Entry h w) :
    Framed (.child index w token) h := before
theorem Framed.bind {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
    {head : Shape body} {tail : ∀value,Shape (next value)} (front : Framed head h)
    (rest : ∀value middle,runPrefixOuter body h=(.ok value,middle)→Framed (tail value) middle) :
    Framed (.bind head tail) h := ⟨front,rest⟩
theorem Framed.marked (label : Label) (w : World) (before : CompleteProduct.Carrier h w)
    (body : Framed shape h) : Framed (.marked label w shape) h := ⟨before,body⟩

structure ChildSourceContract (native inside : ChildPoints) (Good : History → World → Prop)
    {α : Type} {action : PrefixM Event α} (token : Child action) where
  remainder : ∀w h u middle,native _ _ token w h u middle→PrefixM Event α
  continuation : ∀w h u middle (point : native _ _ token w h u middle),
    runPrefix action w h=runPrefix (remainder w h u middle point) u middle
  coverage : ∀w h u middle,native _ _ token w h u middle→inside _ _ token w h u middle
  safe : ∀w h u middle,token.Entry h w→inside _ _ token w h u middle→Good middle u

structure ChildContracts (native inside : ChildPoints) (Good : History → World → Prop) where
  dispatch : ∀call,ChildSourceContract native inside Good (.dispatch call)
  sends : ChildSourceContract native inside Good .sends
  idle : ChildSourceContract native inside Good .idle
  afterXmit : ChildSourceContract native inside Good .afterXmit
  advance : ChildSourceContract native inside Good .advance

variable {native inside : ChildPoints} {Good : History→World→Prop}

def ChildContracts.at (children : ChildContracts native inside Good) (token : Child action) :
    ChildSourceContract native inside Good token := by
  cases token with
  | dispatch call => exact children.dispatch call
  | sends => exact children.sends
  | idle => exact children.idle
  | afterXmit => exact children.afterXmit
  | advance => exact children.advance

theorem Point.coverage (children : ChildContracts native inside Good)
    (point : Point native shape h site u middle) : Point inside shape h site u middle := by
  induction point with
  | nativeEntry token => exact .nativeEntry token
  | nativeReturn token performed => exact .nativeReturn token performed
  | childEntry token => exact .childEntry token
  | childReturn token performed => exact .childReturn token performed
  | interior token point => exact .interior token ((children.at token).coverage _ _ _ _ point)
  | left tail _ ih => exact .left tail ih
  | right head tail leading _ ih => exact .right head tail leading ih
  | snapshot label w body => exact .snapshot label w body
  | marked label w _ ih => exact .marked label w ih

theorem Point.safe (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) (framed : Framed shape h)
    (point : Point inside shape h site u middle) : Good middle u := by
  induction point with
  | nativeEntry token => exact carrierGood _ _ framed
  | nativeReturn token performed => exact carrierGood _ _ (token.normal framed performed)
  | childEntry token => exact carrierGood _ _ (token.entry_carrier framed)
  | childReturn token performed => exact carrierGood _ _ (token.normal framed performed)
  | interior token point => exact (children.at token).safe _ _ _ _ framed point
  | left tail _ ih => exact ih framed.1
  | right head tail leading _ ih => exact ih (framed.2 _ _ leading)
  | snapshot label w body => exact carrierGood _ _ framed.1
  | marked label w _ ih => exact ih framed.2


def Covered (inside : ChildPoints) (Good : History → World → Prop)
    (shape : Shape action) (h : History) : Prop :=
  ∀site u middle,Point inside shape h site u middle→Good middle u

theorem covered (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) (framed : Framed shape h) :
    Covered native Good shape h :=
  fun _ _ _ point => Point.safe carrierGood children framed (point.coverage children)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
