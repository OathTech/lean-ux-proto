import Leanux.Proofs.WG.Config.RequestFinalHeaderClaims
import Leanux.Proofs.WG.Config.KeyIdentityReadbackClaims

/-! Actual sequential mixed setter/getter readback with original-entry header and private bytes. Selector and idle socket inputs are transported from the original entry; existing static getter conditions remain explicit. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem certificate_mixed_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (selected : ClaimView.selectsDevice initial before)
    (key : Key) (given : attrs.privateKey=some key)
    (d : Device) (present : middle.wg.device=some d) (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : initial.wg.nlSock7.cbRunning=false) (emptyQueue : initial.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Fields attrs before d ∧ PortSelected attrs before d.incomingPort ∧
      d.staticIdentity.staticPrivate=
        (if before.staticIdentity.staticPrivate=key then key else clamp key) ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal initial.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none := by
  dsimp only
  obtain ⟨current,currentPresent,fields,port,value⟩:=
    certificate_final_private cs loans attrs initial inspected certificate pre ret middle normal
      r member kind before first key given
  have same : current=d:=Option.some.inj (currentPresent.symm.trans present)
  subst current
  have context:=certificate_context attrs initial inspected certificate ret middle normal before d first present
  have selector:=certificate_selector attrs initial inspected certificate ret middle normal
    before d first present fields selected
  obtain ⟨_,_,_,last,equal,device,socket,held⟩:=certificate_key_mixed_readback
    cs loans attrs initial inspected certificate pre ret middle normal r member kind
    d present data selector ready headerFits cursorData
    (by simpa only [context.1] using idle) (by simpa only [context.1] using emptyQueue)
    within outcome matched
  exact ⟨fields,port,value,last,equal,device,by simpa only [context.1] using socket,held⟩

end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
