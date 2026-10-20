import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointFraming

/-! Fixed-source point composition. The shape parameter is data, not a proof
whose irrelevance could identify arbitrary factorizations. Public dispatch
contracts specialize it to the canonical original-source witnesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev ChildPoints := (α : Type) → (action : PrefixM Event α) → Child action →
  World → History → World → History → Prop

inductive Site where
  | entry
  | returned
  | interior
  | stored
  | scalar
  | left (site : Site)
  | right (site : Site)
  | marked (label : Label) (site : Site)

inductive Point (inside : ChildPoints) : {α : Type} → {action : PrefixM Event α} →
    Shape action → World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point inside shape w h .entry w h
  | returned (shape : Shape action)
      (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Point inside shape w h .returned u middle
  | interior (token : Child action) (point : inside _ _ token w h u middle) :
      Point inside (.child token) w h .interior u middle
  | stored (point : ProductStore.Point source w u) :
      Point inside (.native (.stored source)) w h .stored u h
  | scalar (point : ProductScalar.Point source w u) :
      Point inside (.native (.scalar source)) w h .scalar u h
  | left {body : PrefixM Event α} {next : α → PrefixM Event β}
      {head : Shape body} (tail : ∀ value, Shape (next value)) (point : Point inside head w h site u middle) :
      Point inside (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β} (head : Shape body)
      (tail : ∀ value, Shape (next value))
      (leading : runPrefix body w h = (.ok (value,u),middle))
      (point : Point inside (tail value) u middle site v last) :
      Point inside (.bind head tail) w h (.right site) v last
  | marked (label : Label) (point : Point inside shape w h site u middle) :
      Point inside (.marked label shape) w h (.marked label site) u middle

/-- Each supplied child family must cover its actual native source points at
exactly the same world and history and retain its original continuation.
Continuation equality never constructs a point. -/
structure ChildSourceContract (native inside : ChildPoints) (Good : History → World → Prop)
    {α : Type} {action : PrefixM Event α} (token : Child action) where
  remainder : ∀ w h u middle, native _ _ token w h u middle → PrefixM Event α
  continuation : ∀ w h u middle (point : native _ _ token w h u middle),
    runPrefix action w h = runPrefix (remainder w h u middle point) u middle
  coverage : ∀ w h u middle, native _ _ token w h u middle → inside _ _ token w h u middle
  safe : ∀ w h u middle, token.Entry h w → inside _ _ token w h u middle → Good middle u

/-- These fourteen families are the original WG dispatch bodies. Native
filesystem, seccomp, socket plumbing and quiet control projection frames do
not require a circular contract for dispatch itself. -/
structure ChildContracts (native inside : ChildPoints) (Good : History → World → Prop) where
  config : ∀attrs,ChildSourceContract native inside Good (.family (.config attrs))
  create : ChildSourceContract native inside Good (.family .create)
  delete : ChildSourceContract native inside Good (.family .delete)
  openDevice : ChildSourceContract native inside Good (.family .open)
  down : ChildSourceContract native inside Good (.family .down)
  transmit : ∀family addr payload opts,ChildSourceContract native inside Good (.family (.transmit family addr payload opts))
  receive : ∀family port message tos ll dest,ChildSourceContract native inside Good (.family (.receive family port message tos ll dest))
  flood : ∀count port family messages,ChildSourceContract native inside Good (.family (.flood count port family messages))
  batch : ∀items,ChildSourceContract native inside Good (.family (.batch items))
  dumpDevice : ∀ref,ChildSourceContract native inside Good (.family (.dumpDevice ref))
  dumpStart : ∀fd ref,ChildSourceContract native inside Good (.family (.dumpStart fd ref))
  dumpReceive : ∀fd,ChildSourceContract native inside Good (.family (.dumpReceive fd))
  idle : ChildSourceContract native inside Good (.family .idle)
  delivery : ChildSourceContract native inside Good (.family .delivery)

variable {native inside : ChildPoints} {Good : History → World → Prop}

def ChildContracts.at (contracts : ChildContracts native inside Good) (token : Child action) :
    ChildSourceContract native inside Good token := by
  cases token with
  | family source =>
    cases source with
    | config attrs => exact contracts.config attrs
    | create => exact contracts.create
    | delete => exact contracts.delete
    | «open» => exact contracts.openDevice
    | down => exact contracts.down
    | transmit family addr payload opts => exact contracts.transmit family addr payload opts
    | receive family port message tos ll dest => exact contracts.receive family port message tos ll dest
    | flood count port family messages => exact contracts.flood count port family messages
    | batch items => exact contracts.batch items
    | dumpDevice ref => exact contracts.dumpDevice ref
    | dumpStart fd ref => exact contracts.dumpStart fd ref
    | dumpReceive fd => exact contracts.dumpReceive fd
    | idle => exact contracts.idle
    | delivery => exact contracts.delivery

theorem Point.coverage (contracts : ChildContracts native inside Good)
    (point : Point native shape w h site u middle) : Point inside shape w h site u middle := by
  induction point with
  | entry shape => exact .entry shape
  | returned shape performed => exact .returned shape performed
  | interior token point => exact .interior token ((contracts.at token).coverage _ _ _ _ point)
  | stored point => exact .stored point
  | scalar point => exact .scalar point
  | left tail point ih => exact .left tail ih
  | right head tail leading point ih => exact .right head tail leading ih
  | marked label point ih => exact .marked label ih

/-- Coverage uses the original successful bind prefix. Failed actions have no
returned world; their entry and any supplied actual interior remain available. -/
theorem Point.safe (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (before : Framed shape w h)
    (point : Point inside shape w h site u middle) : Good middle u := by
  induction point with
  | entry shape => exact carrierGood _ _ before.carrier
  | returned shape performed => exact carrierGood _ _ (before.normal performed)
  | interior token point => exact (contracts.at token).safe _ _ _ _ before point
  | stored point => exact carrierGood _ _ (point.carrier before)
  | scalar point => exact carrierGood _ _ (point.carrier before)
  | left tail point ih => exact ih before.1
  | right head tail leading point ih => exact ih (before.2 _ _ _ leading)
  | marked label point ih => exact ih before


def Covered (inside : ChildPoints) (Good : History → World → Prop)
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point inside shape w h site u middle → Good middle u

theorem covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (shape : Shape action)
    (before : Framed shape w h) : Covered native Good shape w h :=
  fun _ _ _ point => Point.safe carrierGood contracts before (point.coverage contracts)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
