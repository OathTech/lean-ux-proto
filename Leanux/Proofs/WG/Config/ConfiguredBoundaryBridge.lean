import Leanux.Proofs.WG.Config.ConfiguredBoundaryEffects
import Leanux.Proofs.WG.Index.ConfigurationCoreBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

def Ready (g : WGWorld) : Prop :=
  ∃ d, g.dev=some d ∧ DeviceReady d

def Selected (pid : PeerId) (g : WGWorld) : Prop :=
  Ready g ∧ pid ∈ BaseCoherence.slots g

def Entry (cs : Ledger) (loans : Reservations) (g : WGWorld) : Prop :=
  Index.ConfigurationIndex.Entry cs loans g ∧ Ready g

def SelectedEntry (cs : Ledger) (loans : Reservations) (pid : PeerId) (g : WGWorld) : Prop :=
  Entry cs loans g ∧ pid ∈ BaseCoherence.slots g

theorem entry_snapshot (cs : Ledger) (loans : Reservations) (g : WGWorld) (a : Ambient) :
    ProjectedEntry cs loans (Campaign2.snapshot g a) ↔ Entry cs loans g := by
  exact and_congr (Index.configurationInput_snapshot cs loans g a) Iff.rfl

theorem selected_snapshot (cs : Ledger) (loans : Reservations) (pid : PeerId)
    (g : WGWorld) (a : Ambient) :
    ProjectedSelected cs loans pid (Campaign2.snapshot g a) ↔ SelectedEntry cs loans pid g := by
  constructor
  · rintro ⟨pre,d,device,member⟩
    refine ⟨(entry_snapshot cs loans g a).mp pre,?_⟩
    change g.dev=some d at device
    simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using member
  · rintro ⟨pre,member⟩
    obtain ⟨d,device,_⟩ := pre.2
    refine ⟨(entry_snapshot cs loans g a).mpr pre,d,device,?_⟩
    simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using member

end Leanux.Proofs.WG.Config.OwnerConfiguration
