import Leanux.Kernel.Defs

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

abbrev FixtureDevices := List (String × Nat × Option String)

def readbackFrame (w : WGWorld) (sock : NlSock) (fixtures : FixtureDevices) : Prop :=
  w.nlSock7 = sock ∧ w.fixtureNetDevices = fixtures

end Leanux.Proofs.WG.Config
