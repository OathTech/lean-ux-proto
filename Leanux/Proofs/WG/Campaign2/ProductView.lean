import Leanux.Proofs.WG.Campaign2.View

/-! Product computations also observe the fixture data present in the original
campaign projection. Exact outcome equality therefore retains those frame
obligations, including for arbitrary product callbacks. -/
namespace Leanux.Proofs.WG.Campaign2.Product
open Leanux

structure Fixture where
  listenerV4 : List (Nat × List UInt8)
  listenerV6 : List (Nat × List UInt8)
  napiBeforePut : List Bool
  napiAmbiguous : Nat
  routesPending : Bool
  routes : List (Nat × Nat × Nat)
  senderInbox : List InboxDatagram
  netnsCHolders : List Nat

structure Snapshot extends Campaign2.Snapshot where
  fixture : Fixture

abbrev Outcome (α : Type) := Except Stop (α × Snapshot)

end Leanux.Proofs.WG.Campaign2.Product
