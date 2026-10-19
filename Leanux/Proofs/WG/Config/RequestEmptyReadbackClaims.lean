import Leanux.Proofs.WG.Config.RequestTerminalClaims
import Leanux.Proofs.WG.Config.GetterReadyClaims
import Leanux.Proofs.WG.Config.RequestReadbackReturnSource
/-! Empty-history normal requests preserve the entire projected WG state. The original sequential getter is total from initial readability, plan, socket and selector premises. Ambient state is not asserted unchanged. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG AllowedIps

theorem certificate_empty_mixed_getter (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (ret : Int) (middle : Campaign2.Snapshot)
    (normal : inspected.outcome = .ok (ret,middle)) (empty : inspected.receipts = [])
    (d : Device) (device : initial.wg.device = some d)
    (selected : ClaimView.selectsDevice initial d)
    (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready))
    (idle : initial.wg.nlSock7.cbRunning = false) (emptyQueue : initial.wg.nlSock7.queue = [])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready
    Campaign2.Returns (wgGetDevice (byIndex d)) (fun s => s = middle)
      (fun result s => result = .ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device = some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7 = socketReadbackFinal initial.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none) := by
  dsimp only
  have same := certificate_empty_wg attrs initial inspected certificate ret middle normal empty
  have getter := readable_mixed_getter_returns d initial.wg.nlSock7 data ready
    headerFits cursorData idle emptyQueue within
  intro g a aligned
  apply getter g a
  rw [aligned]
  refine ⟨same ▸ device,same ▸ rfl,?_⟩
  simpa only [ClaimView.selectsDevice,same] using selected

theorem certificate_empty_mixed_readback (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (ret : Int) (middle : Campaign2.Snapshot)
    (normal : inspected.outcome = .ok (ret,middle)) (empty : inspected.receipts = [])
    (d : Device) (device : initial.wg.device = some d)
    (selected : ClaimView.selectsDevice initial d)
    (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready))
    (idle : initial.wg.nlSock7.cbRunning = false) (emptyQueue : initial.wg.nlSock7.queue = [])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready
    middle.wg = initial.wg ∧
    ∃ final, outcome = .ok ((ret,.ok (mixedGetterJson d
      (routingReadPeer d) (routingReadNode d))),final) ∧
      final.wg.device = some (mixedPagesDevice d pages) ∧
      final.wg.nlSock7 = socketReadbackFinal initial.wg.nlSock7 d ∧
      CursorHeld d (mixedPagesDevice d pages) none := by
  refine ⟨certificate_empty_wg attrs initial inspected certificate ret middle normal empty,?_⟩
  have getter := certificate_empty_mixed_getter attrs initial inspected certificate
    ret middle normal empty d device selected data ready headerFits cursorData idle emptyQueue within
  obtain ⟨dump,final,run,effects⟩ := readback_matches_returns attrs d initial inspected
    outcome matched ret middle normal _ getter
  exact ⟨final,by simpa only [effects.1] using run,effects.2⟩

theorem original_empty_mixed_readback (attrs : DeviceAttrs) (d : Device) (sock : NlSock)
    (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg := true} ready
    Campaign2.Observes (do
      let ret ← wgSetDevice attrs
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun initial outcome => ∃ inspected : Inspection,
        Certificate attrs initial inspected ∧ ReadbackMatches attrs d initial inspected outcome ∧
        ∀ ret middle, inspected.outcome = .ok (ret,middle) → inspected.receipts = [] →
          middle.wg = initial.wg ∧
          ∃ final, outcome = .ok ((ret,.ok (mixedGetterJson d
            (routingReadPeer d) (routingReadNode d))),final) ∧
            final.wg.device = some (mixedPagesDevice d pages) ∧
            final.wg.nlSock7 = socketReadbackFinal sock d ∧
            CursorHeld d (mixedPagesDevice d pages) none) := by
  dsimp only
  intro g a pre
  refine ⟨inspection attrs g a,inspection_certificate attrs g a,
    ⟨g,a,rfl,rfl,rfl⟩,?_⟩
  intro ret middle normal empty
  have result := certificate_empty_mixed_readback attrs (Campaign2.snapshot g a)
    (inspection attrs g a) (inspection_certificate attrs g a) ret middle normal empty
    d pre.1 pre.2.1 data ready headerFits cursorData
    (by simpa only [pre.2.2] using idle) (by simpa only [pre.2.2] using emptyQueue)
    within _ ⟨g,a,rfl,rfl,rfl⟩
  simpa only [pre.2.2] using result

end Leanux.Proofs.WG.Config.RequestOrder
