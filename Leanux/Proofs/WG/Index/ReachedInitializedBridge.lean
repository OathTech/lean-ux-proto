import Leanux.Proofs.WG.Index.ReachedInitializedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedInitialized
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem ActualAccount.bounds {trace : Runner.Trace} {placeholders : Bool} {json : Json}
    {final : Campaign2.Product.Snapshot} (account : ActualAccount trace placeholders json final) :
    InitializedBounds.EndpointSafe final.toSnapshot := by
  obtain ⟨w,history,ledger,_,rfl,_,entry⟩ := account
  exact InitializedBounds.holder_entry_projection ledger [] history w entry

end Leanux.Proofs.WG.Index.ReachedInitialized
