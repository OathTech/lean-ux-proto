import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationFrames
import Leanux.Proofs.WG.Packets.PublicationIngress

/-! Native ingress overwrites only UNCRYPTED or DEAD packet slots. Every
surviving CRYPTED neighbour retains its exact authentication anchor and stamp. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

theorem newRxSkb_preserves (pkt : RxPacket) (state : pkt.state ≠ .crypted)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (newRxSkb pkt) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a id v b hi hr
  obtain ⟨d,hd,rfl,hv,_,_⟩ := RxOrigin.allocation_record pkt ⟨id,w,v,a,b⟩ hr
  dsimp only at hd hv
  subst v
  have device : (Packets.update w (fun u => {u with rxSkbs := u.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1})).dev = some {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1} := by simp [Packets.update,hd]
  apply hi.transport
  · intro slot packet cell crypted
    have stored : (d.rxSkbs.insert d.nextSkb pkt)[slot]? = some packet := by
      simpa [RxDisposition.nativeRxStore,device] using cell
    by_cases same : d.nextSkb = slot
    · subst slot
      have eq : packet = pkt := by simpa using stored.symm
      subst packet
      exact False.elim (state crypted)
    · refine ⟨?_,by simp [packetStamp,device,hd]⟩
      have old : d.rxSkbs[slot]? = some packet := by
        simpa [Std.TreeMap.getElem?_insert,same] using stored
      simp [RxDisposition.nativeRxStore,hd,old]

theorem setRxSkb_state_preserves (id : SkbId) (state : PacketState) (notCrypted : state ≠ .crypted)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (setRxSkb id fun p => {p with state}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hd : w.dev with
  | none => simp [setRxSkb,liftSkb_run,hd] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,hd,hp,
        invariant,AmbientM.invariant] at hr
      cases hr
    | some pkt =>
      rw [Packets.setRxSkb_run w a d id pkt (fun p => {p with state}) hd hp] at hr
      cases hr
      have device : (Packets.update w (fun d => {d with rxSkbs := d.rxSkbs.insert id {pkt with state}})).dev =
          some {d with rxSkbs := d.rxSkbs.insert id {pkt with state}} := by simp [Packets.update,hd]
      apply hi.transport
      · intro slot packet cell crypted
        have stored : (d.rxSkbs.insert id {pkt with state})[slot]? = some packet := by
          simpa [RxDisposition.nativeRxStore,device] using cell
        by_cases same : id = slot
        · subst slot
          have eq : packet = {pkt with state} := by simpa using stored.symm
          subst packet
          exact False.elim (notCrypted crypted)
        · refine ⟨?_,by simp [packetStamp,device,hd]⟩
          have old : d.rxSkbs[slot]? = some packet := by
            simpa [Std.TreeMap.getElem?_insert,same] using stored
          simp [RxDisposition.nativeRxStore,hd,old]

theorem publish_noncrypted_preserves (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted) (history : List TransportDriver.OriginEvent) :
    Preserves (Inv history) (RxWorkers.publishSource id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pid v b hi hr
  obtain ⟨d,pkt,key,p,hd,_,_,_,_,effect⟩ := publish_execution id state w v a b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  have around := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PublicationHistory.publish_around id state) w a pid v b hr
  have epoch := congrArg Prod.fst around
  apply hi.transport
  · intro slot packet cell crypted
    by_cases same : slot = id
    · subst slot
      have selected : packet = {pkt with state} := by
        simpa [RxDisposition.nativeRxStore,hv] using cell.symm
      subst packet
      exact False.elim (notCrypted crypted)
    · have other := congrFun (congrArg (fun s => s.2.1) around) slot
      change (if slot = id then none else (RxDisposition.nativeRxStore v).2 slot) =
        (if slot = id then none else (RxDisposition.nativeRxStore w).2 slot) at other
      rw [ite_eq_right same,ite_eq_right same] at other
      exact ⟨other.symm.trans cell,
        congrArg (fun e : Option Nat => (e.getD 0,slot+1)) epoch⟩

theorem modifyDev_preserves (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (packets : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (modifyDev f) := by
  unfold modifyDev
  apply hoare_modify
  intro w hi
  apply hi.transport
  intro slot pkt cell _
  constructor
  · simpa only [RxDisposition.nativeRxStore,Option.bind_map,Function.comp_def,packets] using cell
  · simp [packetStamp,Option.map_map,Function.comp_def,epoch]

end Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
