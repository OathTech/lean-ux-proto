import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentDescriptorPhases

/-! Concrete environment/descriptor lifecycle roots derive every phase from
original caller inputs. Deletion retains the original native companions;
only the five deeper lifecycle families require interior contracts.
Compound native leaves expose their actual entry and normal-return cuts.
Finer interiors of newlink, destructor check and compound quiet native calls
remain separate obligations, not an initialized completeness claim. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points

noncomputable def dispatchCreateShape : Shape (dispatchCreateObserved (E:=Event)) :=
  .marked .dispatchCreate (Descriptor.originalRequest createShape)
noncomputable def dispatchDeleteShape : Shape (dispatchDeleteObserved hooks) :=
  .marked .dispatchDelete (Descriptor.originalRequest originalDelete)
noncomputable def socketUpShape : Shape (retainedObserved hooks .wgUp) :=
  Descriptor.originalSocket SENDER_FD originalUp
noncomputable def socketDownShape : Shape (retainedObserved hooks .wgDown) :=
  Descriptor.originalSocket SENDER_FD originalDown

theorem delete_input (before : CompleteRunner.DeleteFrames.Entry h w) : Framed originalDelete w h := by
  obtain ⟨history,cs,entry⟩ := before.2.1.1
  exact original_delete_framed ⟨before.1,entry.2,entry.1.1.2.1,before.2.1.2,before.2.2⟩

theorem dispatch_create_framed (before : CompleteProduct.Carrier h w) : Framed dispatchCreateShape w h :=
  Descriptor.original_request_framing Descriptor.stable_product createShape
    (fun _ _ before=>create_framed before.1) h w before

theorem dispatch_delete_framed (before : CompleteRunner.DeleteFrames.Entry h w) : Framed dispatchDeleteShape w h :=
  Descriptor.original_request_framing Descriptor.stable_delete originalDelete
    (fun _ _ before=>delete_input before) h w before

theorem socket_up_framed (before : CompleteProduct.Carrier h w) : Framed socketUpShape w h :=
  Descriptor.original_socket_framing Descriptor.stable_product SENDER_FD originalUp
    (fun _ _ before=>original_up_framed before) h w before

theorem socket_down_framed (before : CompleteProduct.Carrier h w) : Framed socketDownShape w h :=
  Descriptor.original_socket_framing Descriptor.stable_product SENDER_FD originalDown
    (fun _ _ before=>original_down_framed before.1) h w before

inductive Root where
  | create | delete | open | down | socketUp | socketDown

def Root.action : Root→PrefixM Event Int
  | .create => dispatchCreateObserved
  | .delete => dispatchDeleteObserved hooks
  | .open => envUpObserved hooks
  | .down => envDownObserved hooks
  | .socketUp => retainedObserved hooks .wgUp
  | .socketDown => retainedObserved hooks .wgDown

def Root.Entry (root : Root) : List Event→World→Prop := match root with
  | .delete => CompleteRunner.DeleteFrames.Entry
  | _ => CompleteProduct.Carrier

noncomputable def canonical : (root : Root)→Shape root.action
  | .create => dispatchCreateShape
  | .delete => dispatchDeleteShape
  | .open => originalUp
  | .down => originalDown
  | .socketUp => socketUpShape
  | .socketDown => socketDownShape

theorem root_framed (root : Root) (before : root.Entry h w) : Framed (canonical root) w h := by
  cases root with
  | create => exact dispatch_create_framed before
  | delete => exact dispatch_delete_framed before
  | «open» => exact original_up_framed before
  | down => exact original_down_framed before.1
  | socketUp => exact socket_up_framed before
  | socketDown => exact socket_down_framed before

theorem execution (root : Root) (performed : runPrefix root.action w h=(result,last)) :
    Execution (canonical root) w h result last := execution_cases _ performed

theorem boundary (root : Root) (before : root.Entry h w)
    (point : Point Boundary (canonical root) w h site u middle) : Account middle u :=
  boundary_carrier (root_framed root before) point

def RootPoints (points : ChildPoints) (root : Root) (w : World) (h : List Event)
    (u : World) (middle : List Event) : Prop := ∃site,Point points (canonical root) w h site u middle

variable {native inside : ChildPoints} {Good : List Event→World→Prop}

theorem root_coverage (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) : RootPoints inside root w h u middle := by
  obtain ⟨site,point⟩:=point
  exact ⟨site,point.coverage children⟩

theorem root_safe (root : Root) (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) (before : root.Entry h w)
    (point : RootPoints inside root w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact point.safe accountGood children (root_framed root before)

theorem root_remainder (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) :
    ∃rest, (∃site,Residual children (canonical root) w h site u middle rest) ∧
      runPrefix root.action w h=runPrefix rest u middle := by
  obtain ⟨site,point⟩:=point
  obtain ⟨rest,residual⟩:=point.residual children
  exact ⟨rest,⟨site,residual⟩,residual.run⟩

noncomputable def remainder (root : Root) (children : ChildContracts native inside Good)
    (w : World) (h : List Event) (u : World) (middle : List Event)
    (point : RootPoints native root w h u middle) : PrefixM Event Int :=
  Classical.choose (root_remainder root children point)

theorem remainder_run (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) :
    runPrefix root.action w h=runPrefix (remainder root children w h u middle point) u middle :=
  (Classical.choose_spec (root_remainder root children point)).2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
