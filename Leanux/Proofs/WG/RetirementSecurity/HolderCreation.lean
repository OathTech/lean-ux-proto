import Leanux.Proofs.WG.RetirementSecurity.HolderPayments

/-! Actual creation produces a temporary occurrence while preserving every
physical holder. Slot vacancy comes from the separately established R2
allocation invariant, rather than from invented credit slack. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Lifetimes

theorem create_carriers (word : Option PeerId) (id : KeypairId)
    (w v : WGWorld) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    carrierShape v = carrierShape w := by
  obtain ⟨d,device,rfl,rfl⟩ := Origins.create_some word w v id a b run
  simp [carrierShape,peersAt,keyAllocationWorld,keyAllocationDevice,device]

theorem HolderAccount.create (account : HolderAccount temporary w)
    (allocation : AllocationInv history w) (word : Option PeerId)
    (id : KeypairId) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    HolderAccount (⟨id,w.keypairCounter + 1⟩ :: temporary) v := by
  obtain ⟨loans,projected,credits⟩ := account
  have created := (credits.create allocation word id a b run).perm List.perm_middle.symm
  exact ⟨loans,durableLoans_transport loans (create_carriers word id w v a b run)
    projected (durable_resident created),created⟩

end Leanux.Proofs.WG.RetirementSecurity
