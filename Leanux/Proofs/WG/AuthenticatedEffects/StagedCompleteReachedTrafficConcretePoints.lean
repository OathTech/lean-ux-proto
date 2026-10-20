import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficFixtureFrames

/-! Every traffic point is a constructor of the fixed source witness.
Service/NAPI interiors keep their canonical point families and continuations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive Site where
  | entry | returned
  | service (site : Service.Points.Site)
  | poll (site : Napi.Points.Site)
  | transmit
  | ingress | stored
  | left (site : Site) | right (site : Site)

inductive Point (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints) :
    {α : Type} → {action : PrefixM Event α} → Shape action → World → History → Site → World → History → Prop where
  | entry (source : Shape action) : Point service napi source w h .entry w h
  | returned (source : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point service napi source w h .returned u middle
  | service (source : Service.Points.Shape action)
      (point : Service.Points.Point service source w h site u middle) :
      Point service napi (.service source) w h (.service site) u middle
  | poll (point : Napi.Points.Point napi Napi.Points.inlineShape w h site u middle) :
      Point service napi .poll w h (.poll site) u middle
  | transmit (point : Fixture.Point ⟨family,addr,packets,mtu⟩ w h u middle) :
      Point service napi (.transmit family addr packets mtu) w h .transmit u middle
  | ingress (point : Ingress.RootPoint msg src w h u middle) :
      Point service napi (.native (.receive msg src)) w h .ingress u middle
  | stored (point : ProductStore.Point source w u) :
      Point service napi (.stored source) w h .stored u h
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point service napi head w h site u middle) :
      Point service napi (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefix body w h=(.ok (value,u),middle))
      (point : Point service napi (tail value) u middle site v last) :
      Point service napi (.bind head tail) w h (.right site) v last

variable {nativeService insideService : Service.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints} {Good : History → World → Prop}

theorem Point.coverage
    (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (point : Point nativeService nativeNapi source w h site u middle) :
    Point insideService insideNapi source w h site u middle := by
  induction point with
  | entry source=>exact .entry source
  | returned source performed=>exact .returned source performed
  | service source point=>exact .service source (point.coverage services)
  | poll point=>exact .poll (point.coverage polls)
  | transmit point=>exact .transmit point
  | ingress point=>exact .ingress point
  | stored point=>exact .stored point
  | left tail point ih=>exact .left tail ih
  | right head tail leading point ih=>exact .right head tail leading ih

theorem Point.remaining {α : Type} {action : PrefixM Event α} {source : Shape action}
    (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (point : Point nativeService nativeNapi source w h site u middle) :
    ∃remaining,runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | service source point=>
      obtain ⟨remaining,residual⟩:=point.residual services
      exact ⟨remaining,residual.run⟩
  | poll point=>
      obtain ⟨remaining,residual⟩:=point.residual polls
      exact ⟨remaining,residual.run⟩
  | transmit point=>exact point.remaining
  | ingress point=>exact point.remaining
  | stored point=>exact point.observed_remaining _
  | left tail point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining >>= _,Scheduler.bind_run_equal _ continued⟩
  | right head tail leading point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining,by rw [runPrefix_bind,leading];exact continued⟩

/-- Security: actual receive/flood/batch source cuts retain the packet
account through canonical scheduling, polling, fixture transmit and the
fixed ingress source. Finer native access intervals remain explicit. -/
theorem Point.safe
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptFront : ∀ledger h w,FrontCuts.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (before : CompleteProduct.Carrier h w) (point : Point insideService insideNapi source w h site u middle) :
    Good middle u := by
  induction point with
  | entry source=>exact accountGood _ _ before.1
  | returned source performed=>exact accountGood _ _ (source.normal before performed).1
  | service source point=>exact point.safe (fun _ _ account=>accountGood _ _ account.1) services before
  | poll point=>exact point.safe accountGood polls before.1
  | transmit point=>exact point.safe accountGood acceptStaging acceptFront acceptPeer before
  | ingress point=>exact point.safe accountGood acceptPeer before
  | stored point=>exact accountGood _ _ (point.carrier before).1
  | left tail point ih=>exact ih before
  | right head tail leading point ih=>exact ih (head.normal before leading)

inductive Root where
  | receive (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat)
  | flood (count port family : Nat) (messages : List (List UInt8))
  | batch (items : List Env.BatchItem)

def Root.action : Root → PrefixM Event Int
  | .receive family port msg tos ll dest=>Driver.injectObserved hooks family port msg tos ll dest
  | .flood count port family messages=>Driver.floodObserved hooks count port family messages
  | .batch items=>Driver.batchObserved hooks items

noncomputable def Root.source (root : Root) : Shape root.action := match root with
  | .receive family port msg tos ll dest=>receiveSource family port msg tos ll dest
  | .flood count port family messages=>floodSource count port family messages
  | .batch items=>batchSource items

def RootPoint (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (root : Root) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point service napi root.source w h site u middle

noncomputable def remainder (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (point : RootPoint nativeService nativeNapi root w h u middle) : PrefixM Event Int :=
  Classical.choose ((Classical.choose_spec point).remaining services polls)

theorem remainder_run (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (point : RootPoint nativeService nativeNapi root w h u middle) :
    runPrefix root.action w h=runPrefix (remainder services polls point) u middle :=
  Classical.choose_spec ((Classical.choose_spec point).remaining services polls)

theorem root_safe
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptFront : ∀ledger h w,FrontCuts.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (before : CompleteProduct.Carrier h w) (point : RootPoint insideService insideNapi root w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact point.safe accountGood acceptStaging acceptFront acceptPeer services polls before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
