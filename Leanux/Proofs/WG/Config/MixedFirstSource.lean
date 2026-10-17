import Leanux.Proofs.WG.Config.MixedFirstModel
import Leanux.Proofs.WG.Config.MixedPageBoundsClaims
import Leanux.Proofs.WG.Config.MixedPageSelectionClaims
import Leanux.Proofs.WG.Config.MixedHeldCallbackSource
import Leanux.Proofs.WG.Config.DeviceTransitionSource
import Leanux.Proofs.WG.Config.PaginationStartSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Original first callback, including the empty-Device guard, from baseline
residency and only the computed nonfinal cursor's acquisition bound. -/
theorem mixedFirst_callback_returns (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorRefs : ∀ id,
      (if (mixedFirstScan d peers nodes).native.2.2.2.1 then none else
        (mixedFirstScan d peers nodes).native.2.1) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = mixedPeersFirstCall d peers nodes ∧
        g.dev = some (mixedFirstDevice d peers nodes)) := by
  by_cases empty : d.peerList = []
  · have callback := wgGetDeviceDump_guard_returns d {hasWg := true} 0
      (by simp [cursorGuardValue,empty]) (by intro _; exact headerFits)
      (by intro id impossible; cases impossible)
    dsimp only at callback
    rw [mixedPageHeader_exact d {hasWg := true} (by intro _; exact headerFits)] at callback
    simpa [mixedPeersFirstCall,mixedPageCall,mixedFirstScan,mixedInitialRows,empty,mixedPeerScan,
      mixedFirstDevice,cursorHandoff,cursorAcquired,cursorReleased] using callback
  · have origin := mixedInitialRows_origin d peers {hasWg := true} rfl
    have selected := mixedBoundary_selected d peers (mixedInitialRows d peers) {hasWg := true} none
      origin.1 origin.2 (by constructor <;> intros <;> contradiction)
    have members := mixedOrigin_members d peers (mixedInitialRows d peers) {hasWg := true} none
      origin.1 origin.2
    have callback := (mixedPage_held_returns d d peers nodes (mixedInitialRows d peers)
      {hasWg := true} 0 (by simp [CursorHeld])
      (fun row member => residents row.1 (members row member).1)
      (fun row member id node => readable row.1 (members row member).1 id ((members row member).2 id node))
      selected.2 (Or.inl rfl) selected.1.symm
      (by simp [cursorGuardValue,empty]) (by intro _; exact headerFits)
      (by intro id impossible; cases impossible)
      (by
        intro id next
        obtain ⟨p,found,positive,bounded⟩ := cursorRefs id next
        exact ⟨p,found,positive,by simpa using bounded⟩)).2
    have old := mixedPeerScan_oldCursor d peers nodes (mixedInitialRows d peers) {hasWg := true} none
      {room := mixedPageRoom d {hasWg := true}} #[]
    dsimp only at old
    intro g ambient device
    obtain ⟨result,final,after,run,value,deviceAfter⟩ := callback g ambient device
    refine ⟨result,final,after,run,?_,?_⟩
    · simpa [mixedPeersFirstCall,mixedPageCall,old,empty,mixedFirstScan] using value
    · rw [deviceAfter]
      rfl

/-- The original idle start executes that callback and retains its real
inline-DONE/spill or nonfinal socket branch and ordered Device effects. -/
theorem mixedFirst_start_returns (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (sock : NlSock)
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorRefs : ∀ id,
      (if (mixedFirstScan d peers nodes).native.2.2.2.1 then none else
        (mixedFirstScan d peers nodes).native.2.1) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31)
    (idle : sock.cbRunning = false) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some (mixedFirstDevice d peers nodes) ∧
        g.nlSock7 = mixedFirstSocket d peers nodes sock) := by
  have callback := mixedFirst_callback_returns d peers nodes residents readable headerFits cursorRefs
  cases done : (mixedFirstScan d peers nodes).native.2.2.2.1 with
  | true =>
    have device : mixedFirstDevice d peers nodes = d := by simp [mixedFirstDevice,done,cursorAcquired]
    have completed : (mixedPeersFirstCall d peers nodes).ret = 0 := by
      simp [mixedPeersFirstCall,mixedPageCall,cursorCallResult,done]
    have cursor : (mixedPeersFirstCall d peers nodes).ctx.nextPeer = none := by
      simp [mixedPeersFirstCall,mixedPageCall,cursorCallResult,done]
    have start := netlinkDumpStart_completed d sock (mixedPeersFirstCall d peers nodes) idle completed cursor
      (by simpa only [device] using callback)
    simpa [mixedFirstSocket,completed,device] using start
  | false =>
    have more : 0 < (mixedPeersFirstCall d peers nodes).ret := by
      simp only [mixedPeersFirstCall,mixedPageCall,cursorCallResult,done,Bool.false_eq_true,ite_false]
      exact mixedPeerScan_nonfinal_ret d peers nodes (mixedInitialRows d peers) {hasWg := true}
    have start := netlinkDumpStart_more_device_transition d (mixedFirstDevice d peers nodes) sock
      (mixedPeersFirstCall d peers nodes) idle more callback
    have notDone : (mixedPeersFirstCall d peers nodes).ret ≠ 0 := by omega
    simpa [mixedFirstSocket,notDone] using start

end Leanux.Proofs.WG.Config
