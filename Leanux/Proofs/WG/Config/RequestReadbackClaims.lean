import Leanux.Proofs.WG.Config.RequestReadbackReturnSource
import Leanux.Proofs.WG.Config.MixedGetterFieldClaims
import Leanux.Proofs.WG.Config.RequestReadbackBridge
import Leanux.Proofs.WG.Config.RequestInputClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

namespace RequestOrder

/-- An actual normal refusal cut, for arbitrary attributes, supplies every
dynamic input to the existing mixed getter. Only static getter readiness is
required at the computed committed prefix. -/
theorem certificate_refusal_mixed_getter (attrs : DeviceAttrs) (d : Device)
    (peers : PeerId → Peer) (nodes : NodeId → AipNode) (sock : NlSock)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (facts : Certificate attrs initial inspected)
    (ret : Int) (middle : Campaign2.Snapshot)
    (normal : inspected.outcome = .ok (ret,middle))
    (entry : initial.wg.device = some d)
    (selected : ClaimView.selectsDevice initial d) (socket : initial.wg.nlSock7 = sock)
    (r : Receipt) (member : r ∈ inspected.receipts) (port : Nat)
    (kind : r.kind = .port port) (nonzero : port ≠ 0) (refused : r.result ≠ 0)

    (residents : ∀ q ∈ d.peerList,d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList,∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (prefixDevice attrs d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (prefixDevice attrs d) peers
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (prefixDevice attrs d)
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
:
    let pages := mixedPages (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready
    ret = (portOutcome (prefixDevice attrs d) port initial.wg.portBound).1 ∧
    Campaign2.Returns (wgGetDevice (byIndex d)) (fun s => s = middle)
      (MixedRefusalReadback attrs d peers nodes sock pages) := by
  dsimp only
  obtain ⟨code,outer,clears,_,sockEq,fixture⟩ := certificate_initial_port_refusal
    attrs initial inspected facts ret middle normal d entry r member port kind nonzero refused
  obtain ⟨current,device,fields⟩ := Option.map_eq_some_iff.mp outer
  have effect : ClearedPeerStore d current d.peerList := by
    simpa only [ClaimView.clearedPeers,device,Option.bind_some,ClearedPeerStore] using clears
  have lookup : ∀ q : PeerId,(current.peers[q]?).map keyGetterPeerView =
      ((prefixDevice attrs d).peers[q]?).map keyGetterPeerView :=
    clearedPeerStore_getter_frame d current d.peerList effect
  have getter := mixed_getter_fields_returns (prefixDevice attrs d) current peers nodes sock
    fields lookup residents readable ready headerFits fresh cursorData within idle emptyQueue
  refine ⟨code,?_⟩
  intro w ambient aligned
  have getPre : (Campaign2.snapshot w ambient).wg.device = some current ∧
      (Campaign2.snapshot w ambient).wg.nlSock7 = sock ∧
      ClaimView.selectsDevice (Campaign2.snapshot w ambient) (prefixDevice attrs d) := by
    rw [aligned]
    refine ⟨device,sockEq.trans socket,?_⟩
    simpa only [ClaimView.selectsDevice,prefixDevice,fixture] using selected
  obtain ⟨dump,out,rest,run,json,values,residentValues,same,finalDevice,finalSocket,held⟩ :=
    getter w ambient getPre
  exact ⟨dump,out,rest,run,json,current,values,fields,effect,residentValues,same,
    finalDevice,finalSocket,held⟩

end RequestOrder

namespace RequestOrder

/-- Every original request outcome has its original receipt certificate.
At a normal refused nonzero-port cut the getter is guaranteed to finish from
that exact returned snapshot, under the static plan conditions below. -/
theorem original_refusal_getter_continuation (attrs : DeviceAttrs) (d : Device)
    (peers : PeerId → Peer) (nodes : NodeId → AipNode) (sock : NlSock)

    (residents : ∀ q ∈ d.peerList,d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList,∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (prefixDevice attrs d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (prefixDevice attrs d) peers
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (prefixDevice attrs d)
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
:
    let pages := mixedPages (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready
    Campaign2.Observes (wgSetDevice attrs)
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun initial outcome => ∃ inspected : Inspection,
        inspected.outcome = outcome ∧ Certificate attrs initial inspected ∧
        ∀ ret middle, inspected.outcome = .ok (ret,middle) →
          ∀ r ∈ inspected.receipts, ∀ port, r.kind = .port port → port ≠ 0 → r.result ≠ 0 →
            ret = (portOutcome (prefixDevice attrs d) port initial.wg.portBound).1 ∧
            Campaign2.Returns (wgGetDevice (byIndex d)) (fun s => s = middle)
              (MixedRefusalReadback attrs d peers nodes sock pages)) := by
  dsimp only
  intro w ambient pre
  refine ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_certificate attrs w ambient,?_⟩
  intro ret middle normal r member port kind nonzero refused
  exact certificate_refusal_mixed_getter attrs d peers nodes sock
    (Campaign2.snapshot w ambient) (inspection attrs w ambient) (inspection_certificate attrs w ambient)
    ret middle normal pre.1 pre.2.1 pre.2.2 r member port kind nonzero refused
    residents readable ready headerFits fresh cursorData within idle emptyQueue

/-- Actual sequential setter/getter readback for arbitrary attributes.
A completed nonzero-port refusal receipt forces the whole pair to return the
computed prefix JSON and the getter's exact cursor effect. Other paths keep
their exact original outcome through ReadbackMatches. -/
theorem original_refusal_mixed_readback (attrs : DeviceAttrs) (d : Device)
    (peers : PeerId → Peer) (nodes : NodeId → AipNode) (sock : NlSock)

    (residents : ∀ q ∈ d.peerList,d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList,∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (prefixDevice attrs d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (prefixDevice attrs d) peers
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (prefixDevice attrs d)
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (prefixDevice attrs d) peers nodes
        (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
:
    let pages := mixedPages (prefixDevice attrs d) peers nodes
      (mixedInitialRows (prefixDevice attrs d) peers) {hasWg := true} ready
    Campaign2.Observes (do
      let ret ← wgSetDevice attrs
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun initial outcome => ∃ inspected : Inspection,
        Certificate attrs initial inspected ∧ ReadbackMatches attrs d initial inspected outcome ∧
        ∀ ret middle, inspected.outcome = .ok (ret,middle) →
          ∀ r ∈ inspected.receipts, ∀ port, r.kind = .port port → port ≠ 0 → r.result ≠ 0 →
            ret = (portOutcome (prefixDevice attrs d) port initial.wg.portBound).1 ∧
            ∃ final, outcome = .ok ((ret,.ok (mixedGetterJson (prefixDevice attrs d) peers nodes)),final) ∧
              MixedRefusalReadback attrs d peers nodes sock pages
                (.ok (mixedGetterJson (prefixDevice attrs d) peers nodes)) final) := by
  dsimp only
  intro w ambient pre
  refine ⟨inspection attrs w ambient,inspection_certificate attrs w ambient,
    ⟨w,ambient,rfl,rfl,rfl⟩,?_⟩
  intro ret middle normal r member port kind nonzero refused
  obtain ⟨code,getter⟩ := certificate_refusal_mixed_getter attrs d peers nodes sock
    (Campaign2.snapshot w ambient) (inspection attrs w ambient) (inspection_certificate attrs w ambient)
    ret middle normal pre.1 pre.2.1 pre.2.2 r member port kind nonzero refused
    residents readable ready headerFits fresh cursorData within idle emptyQueue
  refine ⟨code,?_⟩
  obtain ⟨dump,final,run,effects⟩ := readback_matches_returns attrs d
    (Campaign2.snapshot w ambient) (inspection attrs w ambient) _
    ⟨w,ambient,rfl,rfl,rfl⟩ ret middle normal _ getter
  refine ⟨final,?_,?_⟩
  · simpa only [effects.1] using run
  · simpa only [effects.1] using effects

end RequestOrder

end Leanux.Proofs.WG.Config
