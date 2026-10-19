import Leanux.Proofs.WG.Config.InitializedOwnerClaims
import Leanux.Proofs.WG.Config.RoutingReadbackEffects
import Leanux.Proofs.WG.Config.MixedGetterClaims
import Leanux.Proofs.WG.Config.GetterFreshEffects
import Leanux.Proofs.WG.Config.GetterReadyModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

theorem represented_dump_readable (d : Device) (t4 t6 : Tree)
    (routing : RoutingInvariant d t4 t6) (distinct : d.peerList.Nodup)
    (residents : ∀ pid ∈ d.peerList,∃ p,d.peers[pid]?=some p) :
    DeviceDumpReadable d := by
  have actual : ∀ pid ∈ d.peerList,d.peers[pid]?=some (routingReadPeer d pid) := by
    intro pid member
    obtain ⟨p,present⟩ := residents pid member
    simp only [routingReadPeer,present,Option.getD_some]
  exact ⟨distinct,actual,fun pid member=>(routing.lists pid _ (actual pid member)).1,
    fun pid member=>routingReadNode_readable d t4 t6 pid _ routing (actual pid member)⟩

theorem initialized_dump_readable (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool)
    (json : Lean.Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final))
    (d : Device) (present : final.wg.device=some d) : DeviceDumpReadable d := by
  have owned := InitializedOwner.normal trace shape placeholders json final run d present
  obtain ⟨t4,t6,routing⟩ := owned.1
  have base := (InitializedRouting.normal trace shape placeholders json final run).2.2.1
  exact represented_dump_readable d t4 t6 routing (base.coherent d present).1
    (base.residents d present)

theorem readable_dump_fresh (d : Device) (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true}) :
    MixedPlanFresh d (routingReadPeer d)
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) :=
  mixedPages_fresh_of_nodup d (routingReadPeer d) (routingReadNode d) ready data.1 data.2.2.1

theorem readable_mixed_getter_returns (d : Device) (sock : NlSock)
    (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : sock.cbRunning=false) (emptyQueue : sock.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s=>s.wg.device=some d ∧ s.wg.nlSock7=sock ∧ ClaimView.selectsDevice s d)
      (fun result s=>result=.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device=some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7=socketReadbackFinal sock d ∧ CursorHeld d (mixedPagesDevice d pages) none) :=
  mixed_getter_returns d (routingReadPeer d) (routingReadNode d) sock ready
    data.2.1 data.2.2.2 headerFits (readable_dump_fresh d data ready) cursorData idle emptyQueue within

end Leanux.Proofs.WG.Config
