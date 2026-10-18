import Leanux.Proofs.WG.Index.DataIngressEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem enqueue_entry (id : SkbId) (w v : WGWorld) (a b : Ambient) (ret : Int)
    (run : ((enqueuePerDeviceAndPeerRx id).run w).run a=.ok ((ret,v),b)) :
    ∃d pkt p,w.dev=some d ∧ d.rxSkbs[id]?=some pkt ∧ d.peers[pkt.peer]?=some p := by
  unfold enqueuePerDeviceAndPeerRx at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,x,ax,set,tail⟩ := run
  cases device : w.dev with
  | none => simp [setRxSkb,liftSkb,getDev,device,invariant,AmbientM.invariant] at set; cases set
  | some d =>
    cases packet : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,device,SkbStore.setRx,SkbStore.getRx,packet,invariant,AmbientM.invariant] at set
      change Except.error _ = Except.ok _ at set
      cases set
    | some pkt =>
      have exactSet := Packets.setRxSkb_run w a d id pkt (fun q=>{q with state:=.uncrypted}) device packet
      rw [set] at exactSet
      cases exactSet
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨q,y,ay,read,tail⟩ := tail
      have exactRead := Packets.getRxSkb_run
        (Packets.update w (fun d=>{d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=.uncrypted}}))
        a {d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=.uncrypted}}
        id {pkt with state:=.uncrypted} (by simp [Packets.update,device]) (by simp)
      rw [read] at exactRead
      cases exactRead
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨p,z,az,readPeer,tail⟩ := tail
      obtain ⟨_,_,actual,found,resident⟩ := getPeer_normal pkt.peer _ z p a az readPeer
      have eq : actual={d with rxSkbs:=d.rxSkbs.insert id {pkt with state:=.uncrypted}} :=
        Option.some.inj (found.symm.trans (by simp [Packets.update,device]))
      subst actual
      exact ⟨d,pkt,p,rfl,packet,resident⟩

theorem enqueue_fields (id : SkbId) :
    SameView ConfigurationIndex.fields (enqueuePerDeviceAndPeerRx id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  obtain ⟨d,pkt,p,device,packet,resident⟩ := enqueue_entry id w v a b result run
  obtain ⟨_,cpu,effect⟩ := enqueue_effect device packet resident a b run
  have output := congrArg WGStoreView.dev effect
  change v.dev=some (enqueueDevice d id pkt p result cpu) at output
  simp only [ConfigurationIndex.fields,device,output,Option.map_some,Option.some.injEq]
  have peerFrame := ConfigurationIndex.deviceFields_peerWrite d pkt.peer p
    {p with rxQueue:=p.rxQueue.enqueue id} resident rfl
  unfold enqueueDevice ConfigurationIndex.deviceFields senderDeviceCell at *
  split <;> first | exact peerFrame | rfl

end Leanux.Proofs.WG.Index.DataIngress
