import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxConcreteComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitCaller

/-! Direct transmit points retain the actual descriptor and fixture token.
The routed child supplies its fixed staging and repayment intervals. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Configuration TransmitSecurity CausalJournal
abbrev History := List Event

structure Input where
  family : Nat
  address : Nat
  payload : List UInt8
  options : Env.XmitOpts

def action (input : Input) : PrefixM Event Int :=
  Driver.syscallXmitObserved hooks input.family input.address input.payload input.options

def leading (input : Input) : PrefixM Event Xmit.Decision :=
  Xmit.callPrefix input.family input.address input.payload input.options

def leave (token : Nat) : PrefixM Event Unit := liftWGObserver (hooks.fixtureLeave token)
def put (fd : Fd) : PrefixM Event Unit := liftPrefix (liftFS (fdput fd))
def result (input : Input) (ret : Int) : Int := if ret == 0 then input.payload.length else ret

def afterBody (input : Input) (fd : Fd) (token : Nat) (ret : Int) : PrefixM Event Int := do
  leave token
  put fd
  pure (result input ret)

theorem after_leading (performed : runPrefix (leading input) w h=(.ok (decision,u),middle)) :
    runPrefix (action input) w h=runPrefix (Xmit.callTail input.family input.address input.payload decision) u middle := by
  change runPrefix (Xmit.callPrefix input.family input.address input.payload input.options) w h=_ at performed
  rw [action,Xmit.whole_factor,runPrefix_bind,performed]

theorem after_path (path : Xmit.Path input.family input.address input.payload input.options h w fd acquired packets mtu u) :
    runPrefix (action input) w h=runPrefix
      (RoutedTransmit.action ⟨input.family,input.address,packets,mtu⟩ >>= afterBody input fd h.length)
      u (Xmit.entryHistory input.family input.address packets mtu h) :=
  path.continuation

inductive Point (input : Input) (w : World) (h : History) : World → History → Prop where
  | entry : Point input w h w h
  | leading (performed : runPrefix (leading input) w h=(.ok (decision,u),middle)) : Point input w h u middle
  | routed (path : Xmit.Path input.family input.address input.payload input.options h w fd acquired packets mtu u)
      (point : RoutedTransmit.Point ⟨input.family,input.address,packets,mtu⟩ u
        (Xmit.entryHistory input.family input.address packets mtu h) v last) : Point input w h v last
  | bodyReturned (path : Xmit.Path input.family input.address input.payload input.options h w fd acquired packets mtu u)
      (performed : runPrefix (RoutedTransmit.action ⟨input.family,input.address,packets,mtu⟩) u
        (Xmit.entryHistory input.family input.address packets mtu h)=(.ok (ret,v),last)) : Point input w h v last
  | scopeLeft (path : Xmit.Path input.family input.address input.payload input.options h w fd acquired packets mtu u)
      (performed : runPrefix (RoutedTransmit.action ⟨input.family,input.address,packets,mtu⟩) u
        (Xmit.entryHistory input.family input.address packets mtu h)=(.ok (ret,v),last))
      (left : runPrefix (leave h.length) v last=(.ok ((),q),after)) : Point input w h q after
  | descriptorPut (path : Xmit.Path input.family input.address input.payload input.options h w fd acquired packets mtu u)
      (performed : runPrefix (RoutedTransmit.action ⟨input.family,input.address,packets,mtu⟩) u
        (Xmit.entryHistory input.family input.address packets mtu h)=(.ok (ret,v),last))
      (left : runPrefix (leave h.length) v last=(.ok ((),q),after))
      (paid : runPrefix (put fd) q after=(.ok ((),r),events)) : Point input w h r events
  | returned (performed : runPrefix (action input) w h=(.ok (value,u),middle)) : Point input w h u middle

theorem Point.remaining (point : Point input w h u middle) :
    ∃remaining,runPrefix (action input) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | leading performed=>exact ⟨_,after_leading performed⟩
  | routed path point=>
    exact ⟨RoutedTransmit.remainder point >>= afterBody input _ h.length,
      (after_path path).trans (Scheduler.bind_run_equal _ (RoutedTransmit.remainder_run point))⟩
  | bodyReturned path performed=>
    rw [after_path path,runPrefix_bind,performed]
    exact ⟨_,rfl⟩
  | scopeLeft path performed left=>
    rename_i fd acquired packets mtu start last ret sentWorld
    rw [after_path path,runPrefix_bind,performed]
    simp only [afterBody,runPrefix_bind,left]
    refine ⟨put fd >>= fun _=>pure (result input ret),?_⟩
    rw [runPrefix_bind]
  | descriptorPut path performed left paid=>
    rw [after_path path,runPrefix_bind,performed]
    simp only [afterBody,runPrefix_bind,left,paid]
    exact ⟨pure _,rfl⟩
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point input w h u middle) : PrefixM Event Int :=
  Classical.choose point.remaining

theorem remainder_run (point : Point input w h u middle) :
    runPrefix (action input) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
