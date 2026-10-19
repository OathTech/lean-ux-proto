import Leanux.Proofs.WG.Config.ConfiguredOwnerEffects
import Leanux.Proofs.WG.Queues.DurableHolders

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps Queues.RxCredits

theorem funded_configuredOwners_resident
    (g : WGWorld) (d : Device) (t4 t6 : Tree) (holders : DurableHolders)
    (cs : Ledger) (loans : Reservations)
    (device : g.dev = some d) (funded : holders.Funded cs loans g)
    (owners : ConfiguredOwners d t4 t6) (lists : ResidentLists d t4 t6) :
    ResidentOwnerLists d t4 t6 := by
  apply configuredOwners_resident d t4 t6 owners _ lists
  intro pid member
  have base := funded.aligned.base
  simp only [device,Option.map_some,Option.getD_some] at base
  have mapped : pid ∈ holders.base.map Owner.slot := base.symm ▸ member
  obtain ⟨o,inside,slot⟩ := List.mem_map.mp mapped
  have held : o ∈ holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
  obtain ⟨p,stored⟩ := funded.resident held
  obtain ⟨actual,current,_,found,_⟩ := resident_fields stored
  rw [device] at current
  cases current
  exact ⟨p,by simpa only [slot] using found⟩


end Leanux.Proofs.WG.Config
