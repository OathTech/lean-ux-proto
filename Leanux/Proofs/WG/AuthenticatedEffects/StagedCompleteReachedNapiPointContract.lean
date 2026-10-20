import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointFrames

/-! Fixed-source point composition. The shape parameter is data, not a proof
whose irrelevance could identify arbitrary factorizations. Public scheduler
contracts specialize it to the canonical original-source witnesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev ChildPoints := Child → World → History → World → History → Prop

inductive Site where
  | entry
  | returned
  | interior
  | metadata
  | rx
  | free
  | left (site : Site)
  | right (site : Site)
  | marked (label : Label) (site : Site)

inductive Point (inside : ChildPoints) : {α : Type} → {action : PrefixM Event α} →
    Shape action → World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point inside shape w h .entry w h
  | returned (shape : Shape action)
      (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Point inside shape w h .returned u middle
  | interior (token : Child) (point : inside token w h u middle) :
      Point inside (.child token) w h .interior u middle
  | metadata {α : Type} {body : WG.M α} {source : PeerMetadata.Shape body} {w : World}
      (point : PeerMetadata.Point source w.wg w.ambient v b) :
      Point inside (.native (.metadata body source)) w h .metadata {w with wg:=v,ambient:=b} h
  | rx {α : Type} {body : WG.M α} {source : RxAccess.Shape body} {w : World}
      (point : RxAccess.Point source w.wg w.ambient v b) :
      Point inside (.native (.rx body source)) w h .rx {w with wg:=v,ambient:=b} h
  | free {w : World} (point : SkbAccess.Point (SkbStore.freeRx skb) w.wg w.ambient v b) :
      Point inside (.native (.free skb)) w h .free {w with wg:=v,ambient:=b} h
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
    (token : Child) where
  remainder : ∀ w h u middle, native token w h u middle → PrefixM Event token.Result
  continuation : ∀ w h u middle (point : native token w h u middle),
    runPrefix token.action w h = runPrefix (remainder w h u middle point) u middle
  coverage : ∀ w h u middle, native token w h u middle → inside token w h u middle
  safe : ∀ w h u middle, Carrier h w → inside token w h u middle → Good middle u

/-- Only the actual five deeper callback families require interior contracts. -/
structure ChildContracts (native inside : ChildPoints) (Good : History → World → Prop) where
  counter : ∀ skb packet, ChildSourceContract native inside Good (.counter skb packet)
  consume : ∀ pid packet endpoint, ChildSourceContract native inside Good (.consume pid packet endpoint)
  release : ∀ peer, ChildSourceContract native inside Good (.release peer)
  transmit : ∀ family addr packets mtu, ChildSourceContract native inside Good (.transmit family addr packets mtu)
  receive6 : ∀ bytes, ChildSourceContract native inside Good (.receive6 bytes)

variable {native inside : ChildPoints} {Good : History → World → Prop}

def ChildContracts.at (contracts : ChildContracts native inside Good) (token : Child) :
    ChildSourceContract native inside Good token := by
  cases token with
  | counter skb packet => exact contracts.counter skb packet
  | consume pid packet endpoint => exact contracts.consume pid packet endpoint
  | release peer => exact contracts.release peer
  | transmit family addr packets mtu => exact contracts.transmit family addr packets mtu
  | receive6 bytes => exact contracts.receive6 bytes

theorem Point.coverage (contracts : ChildContracts native inside Good)
    (point : Point native shape w h site u middle) : Point inside shape w h site u middle := by
  induction point with
  | entry shape => exact .entry shape
  | returned shape performed => exact .returned shape performed
  | interior token point => exact .interior token ((contracts.at token).coverage _ _ _ _ point)
  | metadata point => exact .metadata point
  | rx point => exact .rx point
  | free point => exact .free point
  | left tail point ih => exact .left tail ih
  | right head tail leading point ih => exact .right head tail leading ih
  | marked label point ih => exact .marked label ih

/-- Coverage uses the original successful bind prefix. Failed actions have no
returned world; their entry and any supplied actual interior remain available. -/
theorem Point.safe (carrierGood : ∀ h w, Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (before : Carrier h w)
    (point : Point inside shape w h site u middle) : Good middle u := by
  induction point with
  | entry shape => exact carrierGood _ _ before
  | returned shape performed => exact carrierGood _ _ (shape.normal before performed)
  | interior token point => exact (contracts.at token).safe _ _ _ _ before point
  | metadata point =>
      obtain ⟨ledger,account⟩ := before
      exact carrierGood _ _ ⟨ledger,account.same_view point.frame⟩
  | rx point =>
      obtain ⟨ledger,account⟩ := before
      exact carrierGood _ _ ⟨ledger,account.same_view point.frame⟩
  | free point =>
      obtain ⟨ledger,account⟩ := before
      exact carrierGood _ _ ⟨ledger,NapiMetadata.free_account point account⟩
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)
  | marked label point ih => exact ih before


def Covered (inside : ChildPoints) (Good : History → World → Prop)
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point inside shape w h site u middle → Good middle u

theorem covered (carrierGood : ∀ h w, Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (shape : Shape action)
    (before : Carrier h w) : Covered native Good shape w h :=
  fun _ _ _ point => Point.safe carrierGood contracts before (point.coverage contracts)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
