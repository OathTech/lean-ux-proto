import Leanux.Proofs.WG.Config.InitializedRoutingModel
import Leanux.Proofs.WG.Index.ReachedInitializedClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedRouting
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits AllowedIps

theorem holder_base (cs : Ledger) (loans : Reservations) (h : List RxHistory.Event)
    (w : World) (entry : HolderEntry.Inv cs loans h w) :
    BaseReady (Campaign2.Product.snapshot w) := by
  constructor
  · intro d device
    change w.wg.dev=some d at device
    have base := entry.1.1.2.1
    simpa only [BaseCoherence.Inv,BaseCoherence.slots,BaseCoherence.rows,
      device,Option.map_some,Option.getD_some] using base
  · intro d device pid member
    change w.wg.dev=some d at device
    obtain ⟨holders,funded,_⟩ := entry.1.1.1
    have mapped : pid ∈ holders.base.map Owner.slot := by
      rw [funded.aligned.base]
      simpa only [device,Option.map_some,Option.getD_some] using member
    obtain ⟨owner,inside,slot⟩ := List.mem_map.mp mapped
    have held : owner ∈ holders.owners := by
      simp only [DurableHolders.owners,List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
    obtain ⟨p,resident⟩ := funded.resident held
    obtain ⟨actual,actualDevice,_,present,_⟩ := resident_fields resident
    have same : actual=d := Option.some.inj (actualDevice.symm.trans device)
    subst actual
    exact ⟨p,by simpa only [slot] using present⟩

theorem account_base {trace : Runner.Trace} {placeholders : Bool} {json : Json}
    {final : Campaign2.Product.Snapshot}
    (account : Index.ReachedInitialized.ActualAccount trace placeholders json final) :
    BaseReady final := by
  obtain ⟨w,history,ledger,_,rfl,_,entry⟩ := account
  exact holder_base ledger [] history w entry


end Leanux.Proofs.WG.Config.InitializedRouting
