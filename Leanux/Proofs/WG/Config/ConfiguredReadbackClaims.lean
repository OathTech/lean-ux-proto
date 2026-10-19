import Leanux.Proofs.WG.Config.RequestFinalHeaderReadbackClaims
import Leanux.Proofs.WG.Config.ConfiguredDeviceClaims
import Leanux.Proofs.WG.Config.GetterReadyClaims
import Leanux.Proofs.WG.Config.ScalarFinishSource
import Leanux.Proofs.WG.Config.RequestFinalHeaderSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG AllowedIps Queues.RxCredits

theorem projected_entry_dump_readable (cs : Ledger) (loans : Reservations)
    (s : Campaign2.Snapshot) (d : Device)
    (entry : ProjectedEntry cs loans s) (device : s.wg.device=some d) :
    DeviceDumpReadable d := by
  obtain ⟨⟨g,a,same,input⟩,ready⟩:=entry
  subst s
  change g.dev=some d at device
  obtain ⟨actual,present,t4,t6,routing,_⟩:=ready
  have equal : actual=d:=Option.some.inj (present.symm.trans device)
  subst actual
  apply represented_dump_readable d t4 t6 routing
  · simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some]
      using input.1.2.1.1
  · intro pid member
    obtain ⟨actual,p,present,stored⟩:=ScalarFinish.base_resident cs loans pid g input
      (by simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using member)
    have equal : actual=d:=Option.some.inj (present.symm.trans device)
    subst actual
    exact ⟨p,stored⟩

theorem certificate_normal_entry (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (shape : Configuration.DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome=.ok (ret,final)) :
    ProjectedEntry cs loans final :=
  RequestOrder.FinalHeader.matches_normal_ensures attrs initial result certificate.1.1
    ret final normal _ _ (original_device cs loans attrs shape) pre

theorem certificate_dump_readable (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (shape : Configuration.DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome=.ok (ret,final))
    (d : Device) (present : final.wg.device=some d) : DeviceDumpReadable d :=
  projected_entry_dump_readable cs loans final d
    (certificate_normal_entry cs loans attrs shape initial result certificate pre ret final normal) present

end Leanux.Proofs.WG.Config.OwnerConfiguration

namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG Noise TimerDiscipline Configuration
theorem certificate_coherent_mixed_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (selected : ClaimView.selectsDevice initial before)
    (key : Key) (given : attrs.privateKey=some key)
    (d : Device) (present : middle.wg.device=some d)
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
  have data:=OwnerConfiguration.certificate_dump_readable cs loans attrs shape
    initial inspected certificate pre ret middle normal d present
  exact certificate_mixed_readback cs loans attrs initial inspected certificate pre
    ret middle normal r member kind before first selected key given d present data
    ready headerFits cursorData idle emptyQueue within outcome matched
end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
