import Leanux.Proofs.WG.Config.GetterReadyClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

/-- The actual initialized endpoint admits the original complete mixed getter
under its static capacity, cursor-reference and socket bounds. Readability and
pagination freshness are derived from the execution, not supplied. -/
theorem initialized_mixed_readback (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool)
    (json : Lean.Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final))
    (d : Device) (present : final.wg.device=some d)
    (selected : ClaimView.selectsDevice final.toSnapshot d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : final.wg.nlSock7.cbRunning=false) (emptyQueue : final.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s=>s=final.toSnapshot)
      (fun result s=>result=.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device=some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7=socketReadbackFinal final.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none) := by
  dsimp only
  intro g ambient same
  apply readable_mixed_getter_returns d final.wg.nlSock7
    (initialized_dump_readable trace shape placeholders json final run d present)
    ready headerFits cursorData idle emptyQueue within g ambient
  rw [same]
  exact ⟨present,rfl,selected⟩

end Leanux.Proofs.WG.Config

