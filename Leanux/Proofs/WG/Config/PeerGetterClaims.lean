import Leanux.Proofs.WG.Config.PeerGetterSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original finite getter for complete empty-IP peer pages. Every page,
callback, receive and coalescing step is derived from data premises. Cursor
freshness and lifetime data concern only computed nonfinal page boundaries;
other repeated visits and endpoints remain arbitrary. The exact ordered
Device writes are retained, with baseline peer lookups and outer fields. -/
theorem peer_getter_returns (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (empty : ∀ id ∈ d.peerList, (peers id).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ id rest, d.peerList = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (fresh : peerPageBoundaryFresh [] (peerPages peers d d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers d d.peerList))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : peerPageReceiveCount peers d d.peerList ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧
        s.wg.device = some (peerGetterFinalDevice d peers) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d ∧
        CursorHeld d (peerGetterFinalDevice d peers) none) := by
  have actual := peerGetter_drain_source d peers sock residents empty firstFits fresh cursorData emptyQueue
  have drain := getterDrain_pages_source (peerFirstDevice d peers) (peerGetterFinalDevice d peers)
    (peerFirstSocket d peers sock) (socketReadbackFinal sock d) (peerGetterMessages d peers)
    (peerPageReceiveCount peers d d.peerList) (multiPeerJson d peers) actual.2 within
    (coalesce_peerGetterMessages d peers)
  have start := peerFirst_start_returns d peers sock residents empty headerFits firstFits
    (fun cursor more last => (peerPageCursorData_first d peers cursorData cursor more last).2) idle
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (multiPeerJson d peers) ∧
      g.dev = some (peerGetterFinalDevice d peers) ∧
      g.nlSock7 = socketReadbackFinal sock d ∧
      CursorHeld d (peerGetterFinalDevice d peers) none)
  rw [wgGetDevice_source]
  apply returns_bind _ _ start
  intro value g ambient pre
  obtain ⟨result,final,after,run,json,device,socket⟩ := drain g ambient pre
  exact ⟨result,final,after,run,json,device,socket,actual.1⟩

end Leanux.Proofs.WG.Config
