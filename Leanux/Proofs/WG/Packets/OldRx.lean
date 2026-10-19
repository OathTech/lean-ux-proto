import Leanux.Proofs.WG.Packets.OldProduct
import Leanux.Proofs.WG.Queues.RxTransmit

/-! The existing RX observer is focused on the actual projected incoming
journal. Every original RX constructor is retained, including saved scans and
probes; no transmit receipt is manufactured by this embedding. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps

def oldRx (g : RxHistory.Obs α) : PrefixM Event α := oldProduct (RoutingJoint.rxAction g)

theorem oldRx_appends (g : RxHistory.Obs α) : Appends (oldRx g) := oldProduct_appends _

theorem oldRx_old_projects (g : RxHistory.Obs α) :
    ProjectsPrefix oldEvent id (oldRx g) (RoutingJoint.rxAction g) :=
  oldProduct_projects _ (Appends.focus _ _ _)

theorem oldRx_projects (g : RxHistory.Obs α) (hg : Appends g) :
    ProjectsPrefix RxTransmit.globalRx id (oldRx g) g := by
  intro w h
  have outer := oldRx_old_projects g w h
  have inner := RoutingJoint.rxAction_rx hg w (h.filterMap oldEvent)
  have histories : (h.filterMap oldEvent).filterMap RoutingJoint.rxEvent =
      h.filterMap RxTransmit.globalRx := List.filterMap_filterMap
  rw [histories] at inner
  have sameResult := congrArg Prod.fst outer
  have sameHistory := congrArg Prod.snd outer
  rw [sameResult,sameHistory] at inner
  change runPrefix g w (h.filterMap RxTransmit.globalRx) = _
  unfold RxTransmit.globalRx at *
  cases result : (runPrefix (oldRx g) w h).1 <;>
    simpa only [result,Except.map,id_eq,List.filterMap_filterMap,RxTransmit.globalRx] using inner

theorem oldRx_erases {g : RxHistory.Obs α} {a : Leanux.M α}
    (erase : ErasesPrefix g a) : ErasesPrefix (oldRx g) a :=
  oldProduct_erases (focusPrefix_erases RoutingJoint.Event.rx RoutingJoint.rxEvent erase)

theorem oldRx_preserves (initial : FlatTable × FlatTable) (g : RxHistory.Obs α)
    (a : Leanux.M α) (erase : ErasesPrefix g a) (routing : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv initial) (Safe initial) (oldRx g) :=
  oldProduct_projected initial _ _ (Appends.focus _ _ _)
    (RoutingJoint.rxAction_routing erase) (global_completion_lift World.wg initial a routing)

end Leanux.Proofs.WG.TransmitJoint
