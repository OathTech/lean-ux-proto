import Leanux.Proofs.WG.RetirementSecurity.Payments
import Leanux.Proofs.WG.Origins.RetainingLeaves

/-! Frames for key-reference accounting. Peer reference payments and packet
store mutations cannot change key funding; the two reference ledgers remain
distinct even when a TX batch or RX packet carries both kinds of reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

theorem Exact.view (account : Exact credits w) (same : Origins.view v = Origins.view w) :
    Exact credits v := by
  have keys (id : KeypairId) : keyAt v id = keyAt w id := by
    have h := congrArg (fun view => view.bind fun fields => fields.2 id) same
    simpa only [Origins.view,keyAt,Option.bind_map,Function.comp_def] using h
  intro allocation
  simpa only [balance,keys] using account allocation

theorem sameView_preserves (action : WG.M α) (same : SameView Origins.view action)
    (credits : Ledger) : Preserves (Exact credits) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact hi.view ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem peerPut_preserves (peer : Option PeerId) (credits : Ledger) :
    Preserves (Exact credits) (peerPut peer) :=
  sameView_preserves _ (Origins.Retaining.peerPut_material peer) credits

theorem packet_preserves (action : SkbM α) (credits : Ledger) :
    Preserves (Exact credits) (liftSkb action) := by
  apply hoare_liftSkb action
  intro w d store hi device
  intro allocation
  simpa [balance,keyAt,device] using hi allocation

theorem freeTx_preserves (id : SkbId) (credits : Ledger) :
    Preserves (Exact credits) (freeTxSkb id) := packet_preserves _ credits

theorem freeRx_preserves (id : SkbId) (credits : Ledger) :
    Preserves (Exact credits) (freeRxSkb id) := packet_preserves _ credits

end Leanux.Proofs.WG.RetirementSecurity.Credits
