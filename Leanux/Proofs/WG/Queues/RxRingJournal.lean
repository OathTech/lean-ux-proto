import Leanux.Proofs.WG.Queues.RingSource

/-! RX specialization of the shared source-ring refinement. The interface
index is not a fresh lifecycle identity; failed outcomes have no returned World. -/
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged
open Ring.Journal

abbrev Event := Ring.Journal.Event SkbId
abbrev Obs := PrefixM Event

def cell (w : World) : Option (Nat × PtrRing SkbId) :=
  w.wg.dev.map fun d => (d.ifindex, d.decryptQueue)

abbrev Refines := Ring.Source.Refines (ι := SkbId)
abbrev Safe := Ring.Source.Safe (ι := SkbId)
abbrev Inv := Ring.Source.Inv cell
abbrev Initialized := Ring.Source.Initialized (ι := SkbId)

theorem run_append (r : PtrRing α) (xs ys : List (Command α)) :
    Ring.Journal.run r (xs ++ ys) =
      let (h, s) := Ring.Journal.run r xs
      let (h', t) := Ring.Journal.run s ys
      (h ++ h', t) := Ring.Source.run_append r xs ys

theorem Refines.step (hr : Refines initial h r) (c : Command SkbId) :
    Refines initial (h ++ [(step r c).1]) (step r c).2 := Ring.Source.Refines.step hr c

theorem Inv.safe (hi : Inv deviceIndex initial h w) : Safe initial h := Ring.Source.Inv.safe hi

theorem initial_inv (hc : cell w = some (deviceIndex, initial)) : Inv deviceIndex initial [] w :=
  Ring.Source.initial_inv hc

theorem Refines.initialized (hr : Refines (PtrRing.init n) h r) : Initialized n h r :=
  Ring.Source.Refines.initialized hr

end Leanux.Proofs.WG.Queues.RxRing
