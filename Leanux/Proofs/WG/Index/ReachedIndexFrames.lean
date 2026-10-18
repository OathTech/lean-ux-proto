import Leanux.Proofs.WG.Index.ReachedIndexBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace Reached
open Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem core_device {w v : WGWorld} (same : v.dev = w.dev)
    (entry : Core w) : Core v := by
  intro d device
  exact entry d (same.symm.trans device)

theorem entry_store {cs : Ledger} {loans : Reservations}
    {history : List RxHistory.Event} {w v : World}
    (same : productStoreView v = productStoreView w)
    (entry : Entry cs loans history w) : Entry cs loans history v :=
  ⟨HolderEntry.store entry.1 same,
    core_device (congrArg (fun s : ProductStore43 => s.2.2.2.dev) same) entry.2⟩

theorem aux_store {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w v : World}
    (same : productStoreView v = productStoreView w)
    (entry : Aux initial loans before history w) :
    Aux initial loans before history v := by
  have device : v.wg.dev = w.wg.dev :=
    congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  exact ⟨HolderAuxiliary.store entry.1 same,
    BaseCoherence.transport entry.2.1
      (congrArg (fun d : Option Device => BaseCoherence.view {dev := d}) device),
    core_device device entry.2.2⟩
end Reached
end Leanux.Proofs.WG.Index
