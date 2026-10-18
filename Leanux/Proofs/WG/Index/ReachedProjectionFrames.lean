import Leanux.Proofs.WG.Index.ReachedIndexBridge
import Leanux.Proofs.WG.Origins.OwnerControlCalls

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.Reached
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem aux_wg_equal {initial : Ledger} {loans : Reservations}
    {before h : List RxHistory.Event} {w v : World}
    (same : w.wg=v.wg) (pre : Aux initial loans before h w) : Aux initial loans before h v := by
  refine ⟨⟨?_,OwnerControlCalls.store h w v (by rw [same]) pre.1.2.1,?_⟩,?_⟩
  · rcases pre.1.1 with ⟨account,epoch,n,events,ring,refines,cell⟩
    refine ⟨?_,epoch,n,events,ring,refines,?_⟩
    · obtain ⟨suffix,hist,boundary⟩ := account
      exact ⟨suffix,hist,same ▸ boundary⟩
    · change v.wg.dev.map (fun d=>(d.ifindex,d.decryptQueue))=_
      rw [←same]
      exact cell
  · exact same ▸ pre.1.2.2
  · exact same ▸ pre.2

end Leanux.Proofs.WG.Index.Reached
