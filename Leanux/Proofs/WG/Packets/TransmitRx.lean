import Leanux.Proofs.WG.Packets.DirectTransmit
import Leanux.Proofs.WG.Packets.OldRx

/-! The same transmit execution projects to the complete original RX journal,
including original lifetime and probe nesting and every stopped prefix. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

private theorem compose {E F G α : Type} (ρ : E → Option F) (σ : F → Option G)
    {a : PrefixM E α} {b : PrefixM F α} {c : PrefixM G α}
    (ab : ProjectsPrefix ρ id a b) (bc : ProjectsPrefix σ id b c) :
    ProjectsPrefix (fun e => (ρ e).bind σ) id a c := by
  intro w h
  have middle := bc w (h.filterMap ρ)
  have higher := ab w h
  have histories : (h.filterMap ρ).filterMap σ = h.filterMap (fun e => (ρ e).bind σ) :=
    List.filterMap_filterMap
  rw [histories,congrArg Prod.fst higher,congrArg Prod.snd higher] at middle
  cases result : (runPrefix a w h).1 <;>
    simpa only [result,Except.map,id_eq,List.filterMap_filterMap] using middle

theorem transmit_rx (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProjectsPrefix RxTransmit.globalRx id (liftWGObserver (transmit family addr packets mtu))
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  compose oldEvent RoutingJoint.rxEvent
    ((transmit_projects family addr packets mtu).liftWGObserver _ _)
    ((RoutingJoint.access_rx (wgXmitPrefix family addr packets mtu)).liftWGObserver _ _)

theorem direct_rx (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProjectsPrefix RxTransmit.globalRx id (direct family addr payload opts)
      (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) :=
  compose oldEvent RoutingJoint.rxEvent (direct_projects family addr payload opts)
    (RoutingJoint.dispatch_rx _)

theorem multicast_rx (family addr : Nat) :
    ProjectsPrefix RxTransmit.globalRx id (multicast family addr)
      (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  oldRx_projects _ (Appends.focus _ _ _)

end Leanux.Proofs.WG.TransmitJoint
