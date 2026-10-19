import Leanux.Proofs.WG.Config.ReplacementCompletionModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.ReplaceCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Queues.RxCredits Queues.RxCredits.DurableHolders AllowedIps Std.Do Lifetimes

def generated (w : WGWorld) : WGWorld :=
  {w with dev := w.dev.map requestGeneration}

theorem generation_funded (holders : DurableHolders) (cs : Ledger) (loans : Reservations)
    (w : WGWorld) (hi : holders.Funded cs loans w) :
    holders.Funded cs loans (generated w) := by
  refine ⟨hi.aligned.frame ⟨?_,?_,?_⟩,hi.carriers.view ?_⟩
  · cases hd : w.dev <;> simp only [passiveView,generated,hd,Option.map_none,Option.map_some,requestGeneration]
  · cases hd : w.dev <;> simp only [sendView,generated,hd,Option.map_none,Option.map_some,requestGeneration]
  · intro pid batches found
    cases device : w.dev <;> simpa only [handoffTxView,generated,device,Option.map_none,
      Option.map_some,Option.bind_none,Option.bind_some,requestGeneration] using found
  · unfold carrierView peerView rxView Queues.RxCredits.keyView Queues.RxCredits.keyWords Queues.RxCredits.currentCells
    cases hd : w.dev <;> simp only [generated,hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,requestGeneration]

theorem generation_stable (cs : Ledger) (w : WGWorld) (hi : StableRx cs w) :
    StableRx cs (generated w) :=
  hi.view (by cases hd : w.dev <;> simp only [stableView,RxRing.nativeCell,rxView,generated,hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,requestGeneration])

theorem generation_base (w : WGWorld) (hi : BaseCoherence.Inv w) :
    BaseCoherence.Inv (generated w) := by
  simpa only [BaseCoherence.Inv,BaseCoherence.slots,BaseCoherence.rows,
    generated,Option.map_map,Function.comp_def,requestGeneration] using hi

theorem generation_routed (w : WGWorld) (initial : FlatTable × FlatTable)
    (hi : RoutedView (routingView w) initial) :
    RoutedView (routingView (generated w)) initial := by
  have same : routingView (generated w) = routingView w := by cases hd : w.dev <;> simp only [routingView,generated,hd,Option.map_none,Option.map_some]; rfl
  rw [same]
  exact hi

end Leanux.Proofs.WG.Config.ReplaceCompletion
