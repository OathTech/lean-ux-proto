import Leanux.Proofs.WG.Config.MixedGetterDrainSource
import Leanux.Proofs.WG.Config.MixedPlanCoalesceSource
import Leanux.Proofs.WG.Config.MixedGetterModel
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The original finite getter over mixed peer and allowed-IP pages. Every
callback, reference handoff, receive and coalescing step follows from static
data and computed boundary premises. The final Device is the ordered native
effect fold; its held-reference invariant restores baseline lookups. -/
theorem mixed_getter_returns (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (sock : NlSock)
    (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) {hasWg := true})
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh d peers
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData d
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : mixedPageReceiveCount
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready) ≤ 4096) :
    let pages := mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (mixedGetterJson d peers nodes) ∧
        s.wg.device = some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d ∧
        CursorHeld d (mixedPagesDevice d pages) none) := by
  dsimp only
  let pages := mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready
  have actual := mixedGetter_drain_source d peers nodes sock ready residents readable
    headerFits fresh cursorData emptyQueue
  have coalesced : coalesce (mixedPageMessages d pages) = pure (.ok (mixedGetterJson d peers nodes)) := by
    exact coalesce_mixedPages d peers nodes {hasWg := true} ready rfl rfl
  have drain := getterDrain_pages_source (mixedFirstDevice d peers nodes) (mixedPagesDevice d pages)
    (mixedFirstSocket d peers nodes sock) (socketReadbackFinal sock d)
    (mixedPageMessages d pages) (mixedPageReceiveCount pages) (mixedGetterJson d peers nodes)
    actual.2 within coalesced
  have start := mixedFirst_start_returns d peers nodes sock residents readable headerFits
    (mixedFirst_cursor_refs d peers nodes ready cursorData) idle
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (mixedGetterJson d peers nodes) ∧
      g.dev = some (mixedPagesDevice d pages) ∧
      g.nlSock7 = socketReadbackFinal sock d ∧ CursorHeld d (mixedPagesDevice d pages) none)
  rw [wgGetDevice_source]
  apply returns_bind _ _ start
  intro value g ambient pre
  obtain ⟨result,final,after,run,json,device,socket⟩ := drain g ambient pre
  exact ⟨result,final,after,run,json,device,socket,actual.1⟩

end Leanux.Proofs.WG.Config
