import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationIngress

/-! New RX admissions and non-crypted publication cannot fabricate an
allocation certificate for a surviving CRYPTED cell. The exact native packet
writes are checked alongside resident key-core and numeric-frontier frames. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.IngressFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder Origins.Retaining
set_option maxHeartbeats 600000

theorem retains {action : WG.M α}
    (keys : CoreRetains action)
    (frontier : ∀ bound, Preserves (ResidentMaterial.Lower bound) action)
    (packets : ∀ w a result v b, (action.run w).run a = .ok ((result,v),b) →
      ∀ id pkt, (RxDisposition.nativeRxStore v).2 id = some pkt → pkt.state = .crypted →
        (RxDisposition.nativeRxStore w).2 id = some pkt ∧ packetStamp v id = packetStamp w id) :
    Preserves (Bounded h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have core := (ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run
  have lower (d e : Device) (hd : w.dev = some d) (he : v.dev = some e) :
      d.nextKeypairId ≤ e.nextKeypairId := by
    have kept := (hoare_iff_run_ambient _ _ _).mp (frontier d.nextKeypairId)
      w a result v b (by simp [ResidentMaterial.Lower,ResidentMaterial.cursor,hd]) run
    simpa [ResidentMaterial.Lower,ResidentMaterial.cursor,he] using kept
  exact ⟨before.1.retains (packets w a result v b run) lower (fun _ _ _ _ => core _),
    before.2.retains core lower⟩

theorem allocate (pkt : RxPacket) (state : pkt.state ≠ .crypted)
     : Preserves (Bounded h) (newRxSkb pkt) := by
  apply retains (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.newRx pkt)).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame ((ResidentMaterial.skb_allocation_view (SkbStore.newRx pkt)).factor (fun fields => fields.2.1)))
  intro w a id v b hr
  obtain ⟨d,hd,rfl,hv,_,_⟩ := RxOrigin.allocation_record pkt ⟨id,w,v,a,b⟩ hr
  dsimp only at hd hv
  subst v
  have device : (Packets.update w (fun u => {u with rxSkbs := u.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1})).dev = some {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1} := by simp [Packets.update,hd]
  intro slot packet cell crypted
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

theorem set_state (id : SkbId) (state : PacketState) (notCrypted : state ≠ .crypted)
     : Preserves (Bounded h) (setRxSkb id fun p => {p with state}) := by
  apply retains (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.setRx id fun p => {p with state})).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame ((ResidentMaterial.skb_allocation_view (SkbStore.setRx id fun p => {p with state})).factor (fun fields => fields.2.1)))
  intro w a result v b hr
  change ((setRxSkb id fun p => {p with state}).run w).run a = .ok ((result,v),b) at hr
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
      intro slot packet cell crypted
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

theorem publish (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted)  :
    Preserves (Bounded h) (RxWorkers.publishSource id state) := by
  apply retains (ResidentMaterial.core_of_same (publish_core id state))
    (fun _ => ResidentMaterial.NativeFrames.lower_slot_fields (CurrentSlots.publish_fields id state))
  intro w a pid v b hr
  obtain ⟨d,pkt,key,p,hd,_,_,_,_,effect⟩ := publish_execution id state w v a b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  have around := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PublicationHistory.publish_around id state) w a pid v b hr
  have epoch := congrArg Prod.fst around
  intro slot packet cell crypted
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


end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.IngressFrames
