import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServiceExpandedInitialized

/-! Post-transmit work is the actual service source: the original device
read, mixed-work guard, queue bookkeeping, selected crypt branch and send
drain. Its canonical witness introduces no new callback family. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Service.Points
abbrev History := List Event
variable {native inside : ChildPoints} {Good : History → World → Prop}

noncomputable def source : Shape (Driver.afterXmitObserved hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (service_shape_head Driver.cryptObserved; exact cryptShape)
    | (service_shape_head Driver.sendWorkersObserved; exact .child (.family .sends))
    | (service_native_head Env.requireDrained; unfold Env.requireDrained)
    | (service_native_head pendingDeviceUnits; exact .native (.kind (.ambient AmbientM.pendingDeviceUnits)))
    | exact Shape.native (.kind .device)
    | service_shape_step

def RootPoint (inside : ChildPoints) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point inside source w h site u middle

noncomputable def remainder (children : ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoint native w h u middle) : PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).residual children)

theorem remainder_run (children : ChildContracts native inside Good)
    (point : RootPoint native w h u middle) :
    runPrefix (Driver.afterXmitObserved hooks) w h=runPrefix (remainder children w h u middle point) u middle :=
  (Classical.choose_spec ((Classical.choose_spec point).residual children)).run

/-- Every declared post-transmit source point conserves packets under the
shared service children, retaining the real mixed-work refusal and the exact
crypt/send branch. No post-transmit callback safety is assumed separately. -/
theorem root_safe (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w)
    (point : RootPoint native w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact (point.coverage children).safe carrierGood children before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit.Points
