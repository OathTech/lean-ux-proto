import Leanux.Proofs.WG.Index.InitializedFundingModel
import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.InitializedBoundsClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedFunding
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem holder_entry_live (cs : Ledger) (loans : Reservations)
    (history : List RxHistory.Event) (w : World)
    (entry : HolderEntry.Inv cs loans history w) :
    LivePeerCredit (Campaign2.snapshot w.wg w.ambient) := by
  intro d pid p device resident live
  change w.wg.dev = some d at device
  obtain ⟨holders,funded,_⟩ := entry.1.1.1
  have credit := FundedBase.live_base_credit entry.1.1.2.2 entry.1.1.2.1
    funded device resident live
  have member : pid ∈ holders.base.map Owner.slot :=
    List.mem_map.mpr ⟨⟨d.ifindex,pid,p.internalId⟩,credit.1,rfl⟩
  rw [funded.aligned.base] at member
  refine ⟨?_,by have := credit.2; omega⟩
  simpa only [device,Option.map_some,Option.getD_some] using member

end Leanux.Proofs.WG.Index.InitializedFunding
