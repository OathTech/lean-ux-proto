import Leanux.Proofs.Framing.WGKernel

/-! The eleven observations formerly held in the monolithic kernel record
and now owned by WG. This is a pure view, not an execution state. -/
namespace Leanux.Proofs.Framing
open Leanux

@[ext] structure WGOwnedView extends WGStoreView where
  fib4 : Net.Fib.Table
  fib4C : Net.Fib.Table
  timerClk : Option UInt64
  timerEnqueues : Nat

def wgOwnedView (g : WGWorld) : WGOwnedView := {
  toWGStoreView := wgStoreView g
  fib4 := g.routing.fib4
  fib4C := g.routing.fib4C
  timerClk := g.timerClk
  timerEnqueues := g.timerEnqueues
}

end Leanux.Proofs.Framing
