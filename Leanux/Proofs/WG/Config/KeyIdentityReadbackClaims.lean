import Leanux.Proofs.WG.Config.KeyIdentityClaims
import Leanux.Proofs.WG.Config.GetterReadyClaims
import Leanux.Proofs.WG.Config.RequestReadbackReturnSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps
theorem certificate_key_mixed_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (inspected : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : RequestOrder.Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (d : Device) (present : middle.wg.device=some d) (data : DeviceDumpReadable d)
    (selected : ClaimView.selectsDevice middle d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : middle.wg.nlSock7.cbRunning=false) (emptyQueue : middle.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : RequestOrder.ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    ∃ before, r.before.wg.device=some before ∧ KeyStage.IdentityEffect attrs before d.staticIdentity ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal middle.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none := by
  dsimp only
  obtain ⟨before,after,entry,last,identity⟩:=KeyStage.certificate_final_identity
    cs loans attrs initial inspected certificate pre ret middle normal r member kind
  have same : after=d:=Option.some.inj (last.symm.trans present)
  subst after
  refine ⟨before,entry,identity,?_⟩
  have getter := readable_mixed_getter_returns d middle.wg.nlSock7 data ready
    headerFits cursorData idle emptyQueue within
  have exactGetter : Campaign2.Returns (wgGetDevice (byIndex d)) (fun s=>s=middle)
      (fun result s=>result=.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device=some (mixedPagesDevice d
          (mixedPages d (routingReadPeer d) (routingReadNode d)
            (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready)) ∧
        s.wg.nlSock7=socketReadbackFinal middle.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d
          (mixedPages d (routingReadPeer d) (routingReadNode d)
            (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready)) none) := by
    intro g a aligned
    apply getter g a
    rw [aligned]
    exact ⟨present,rfl,selected⟩
  obtain ⟨dump,final,run,effects⟩:=RequestOrder.readback_matches_returns attrs d
    initial inspected outcome matched ret middle normal _ exactGetter
  exact ⟨final,by simpa only [effects.1] using run,effects.2⟩
end Leanux.Proofs.WG.Config

