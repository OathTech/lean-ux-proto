import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointSource

/-! Every canonical witness chooses the original dispatch constructor and its
real wrapper order. No retained default callback can recurse to dispatch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration TransmitSecurity CausalJournal
open RetirementSecurity.NestedPeerRelease
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

noncomputable def socketShape (fd : Nat) (body : Shape action) :
    Shape (socketCallOnWith (fun {_} a=>liftPrefix a) fd action) := by
  apply Shape.marked (.socket fd)
  unfold socketCallOnWith
  apply Shape.bind (.native (.fs (fdget fd)))
  intro f
  split
  · exact .pure _
  · exact .bind body (fun ret=>.bind (.native (.fs (fdput f))) (fun _=>.pure ret))

noncomputable def netlinkShape (body : Shape action) :
    Shape (netlinkRequestWith (fun {_} a=>liftPrefix a) action) := by
  apply Shape.marked .netlink
  unfold netlinkRequestWith
  exact .bind (socketShape NETLINK_FD (.bind (.native (.ambient (AmbientM.skipCut allocCuts)))
    (fun _=>.bind body (fun ret=>.bind (.native (.ambient (AmbientM.skipCut allocCuts))) (fun _=>.pure ret)))))
    (fun ret=>.bind (socketShape NETLINK_FD (.pure 0)) (fun _=>.pure ret))

noncomputable def dumpDeviceShape (ref : DeviceRef) : Shape (dumpDispatch (Driver.nestedOps hooks) (.wgGet ref)) := by
  apply Shape.marked (.dump (.wgGet ref))
  unfold dumpDispatch dumpDispatchWith
  apply netlinkShape
  apply Shape.bind (.child (.family (.dumpDevice ref)))
  intro result
  cases result with
  | error err => exact .pure err
  | ok value => exact .bind (.native (.ambientEdit (fun w=>{w with extraOut := [("device",value)]}))) (fun _=>.pure 0)

noncomputable def dumpStartShape (ref : DeviceRef) : Shape (dumpDispatch (Driver.nestedOps hooks) (.wgGetStart ref)) := by
  apply Shape.marked (.dump (.wgGetStart ref))
  unfold dumpDispatch dumpDispatchWith
  apply socketShape
  apply Shape.bind (.native (.ambient (AmbientM.skipCut allocCuts)))
  intro _
  apply Shape.bind (.native (.stored (ProductStore.netlinkReadShape DUMP_FD)))
  intro sock
  split
  · exact .bind (.native (.ambient (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)))
      (fun _=>.bind (.native (.nlWrite DUMP_FD {sock with bound:=true}))
        (fun _=>.bind (.child (.family (.dumpStart DUMP_FD ref)))
          (fun _=>.bind (.native (.ambient (AmbientM.skipCut allocCuts))) (fun _=>.pure 0))))
  · exact .bind (.child (.family (.dumpStart DUMP_FD ref)))
      (fun _=>.bind (.native (.ambient (AmbientM.skipCut allocCuts))) (fun _=>.pure 0))

noncomputable def dumpReceiveShape : Shape (dumpDispatch (Driver.nestedOps hooks) .wgGetRecv) := by
  apply Shape.marked (.dump .wgGetRecv)
  unfold dumpDispatch dumpDispatchWith
  apply socketShape
  apply Shape.bind (.native (.ambient (AmbientM.skipCut allocCuts)))
  intro _
  apply Shape.bind (.child (.family (.dumpReceive DUMP_FD)))
  intro messages
  cases messages with
  | none => exact .native (.ambient (AmbientM.unsupported _))
  | some messages =>
    apply Shape.bind (.native (.ambient (AmbientM.skipCut allocCuts)))
    intro _
    split
    · exact .bind (.native (.ambient (AmbientM.unsupported _)))
        (fun _=>.bind (.native (.ambientEdit (fun w=>{w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)]}))) (fun _=>.pure 0))
    · exact .bind (.native (.ambientEdit (fun w=>{w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)]}))) (fun _=>.pure 0)

noncomputable def observeShape : Shape (Driver.dispatchObserveObserved hooks) := by
  apply Shape.marked .observation
  unfold Driver.dispatchObserveObserved Driver.observeObserved DeliverySource.observeWith
  apply Shape.bind (.bind (.child (.family .idle)) (fun _=>.bind (.native (.stored ProductStore.observeFrontShape))
    (fun _=>.bind (.child (.family .delivery)) (fun _=>.native (.stored ProductStore.observeFinishShape)))))
  rintro ⟨ret,observed⟩
  exact .bind (.native (.ambientEdit (fun w=>{w with extraOut := ["datagrams","replies","stats"].map fun k=>(k,observed.getObjValD k)})))
    (fun _=>socketShape LISTEN4_FD (.pure ret))

noncomputable def canonical (call : Syscall) : Shape (Driver.dispatchObserved hooks call) := by
  apply Shape.marked (.syscall call)
  cases call <;> simp only [Driver.dispatchObserved,dispatchWith]
  case wgSet attrs => exact netlinkShape (.child (.family (.config attrs)))
  case wgCreate => exact .child (.family .create)
  case wgDelete => exact .child (.family .delete)
  case wgXmit family addr payload opts => exact .child (.family (.transmit family addr payload opts))
  case wgInject family port message tos ll dest => exact socketShape SENDER_FD (.child (.family (.receive family port message tos ll dest)))
  case wgFlood count port family messages => exact .child (.family (.flood count port family messages))
  case wgBatch items _ => exact .child (.family (.batch items))
  case wgObserve => exact observeShape
  case wgGet ref => exact dumpDeviceShape ref
  case wgGetStart ref => exact dumpStartShape ref
  case wgGetRecv => exact dumpReceiveShape
  case wgUp => exact socketShape SENDER_FD (.child (.family .open))
  case wgDown => exact socketShape SENDER_FD (.child (.family .down))
  case wgSetMtu n => exact .native (.control (.mtu n))
  case wgDeladdr family => exact .native (.control (.deladdr family))
  case wgDelroute family named dst plen oif kind metric => exact .native (.control (.delroute family named dst plen oif kind metric))
  case wgAddroute dst plen oif kind metric metricMtu flags => exact .native (.control (.addroute dst plen oif kind metric metricMtu flags))
  case wgAddaddr addr plen => exact .native (.control (.addaddr addr plen))
  case wgAdvance ticks => exact .native (.control (.advance ticks))
  case wgNetnsClose => exact .native (.control .netnsClose)
  case seccompProbe nr args target strict => cases target <;> exact .native (.seccomp _)
  case seccompInstall => exact .native (.seccomp _)
  case seccompPrctl => exact .native (.seccomp _)
  case seccompCapdrop => exact .native (.seccomp _)
  case seccompQuery => exact .native (.seccomp _)
  all_goals exact .native (.fs _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
