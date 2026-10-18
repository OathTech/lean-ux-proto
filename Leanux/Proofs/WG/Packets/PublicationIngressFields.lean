import Leanux.Proofs.WG.Packets.PublicationFrontierLifecycle

/-! The ingress constructors may overwrite arbitrary packet slots. Only final
CRYPTED survivors need their old exact cell, stamp and peer identity; fresh
UNCRYPTED and DEAD cells create no publication obligation. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- Transport over concrete surviving cells permits deletion and non-CRYPTED
replacement. Peer fields are retained independently of receiving-key validity. -/
theorem Inv.transport_cells (hi : Inv history w)
    (packets : ∀ id pkt, (RxDisposition.nativeRxStore v).2 id = some pkt → pkt.state = .crypted →
      (RxDisposition.nativeRxStore w).2 id = some pkt ∧ packetStamp v id = packetStamp w id)
    (monotone : FrontiersLe w v)
    (peers : ∀ (pid : PeerId) (d : Device) (p : Peer), v.dev = some d → d.peers[pid]? = some p →
      ∃ old q, w.dev = some old ∧ old.peers[pid]? = some q ∧
        CurrentIdentity.identity p = CurrentIdentity.identity q) : Inv history v := by
  refine ⟨hi.1.transport packets peers,?_⟩
  intro after ha id pkt hp crypted
  have cell : (RxDisposition.nativeRxStore v).2 id = some pkt := by
    simp [RxDisposition.nativeRxStore,ha,hp]
  obtain ⟨old,stamp⟩ := packets id pkt cell crypted
  obtain ⟨before,hb,hpkt⟩ := Option.bind_eq_some_iff.mp old
  have epoch : before.ifindex = after.ifindex := by
    have equal := congrArg Prod.fst stamp
    simpa [packetStamp,ha,hb] using equal.symm
  exact Nat.lt_of_lt_of_le (hi.2 before hb id pkt hpkt crypted)
    (monotone before after hb ha epoch)

/-- Actual allocation with a non-CRYPTED argument can replace even an old
resident slot; only its surviving crypted neighbours retain obligations. -/
theorem newRxSkb_preserves (pkt : RxPacket) (state : pkt.state ≠ .crypted)
    (history : List RxHistory.Event) : Preserves (Inv history) (newRxSkb pkt) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a id v b hi hr
  obtain ⟨d,hd,rfl,hv,_,_⟩ := RxOrigin.allocation_record pkt ⟨id,w,v,a,b⟩ hr
  dsimp only at hd hv
  subst v
  have device : (Packets.update w (fun u => {u with rxSkbs := u.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1})).dev = some {d with rxSkbs := d.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb+1} := by simp [Packets.update,hd]
  apply hi.transport_cells
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
  · intro before after hb ha _
    cases hd.symm.trans hb
    cases device.symm.trans ha
    exact Nat.le_refl _
  · intro pid after p ha hp
    cases device.symm.trans ha
    exact ⟨d,p,hd,hp,rfl⟩

/-- Source UNCRYPTED/DEAD state stores remove an authorization obligation;
this does not assert preservation for an arbitrary CRYPTED write. -/
theorem setRxSkb_state_preserves (id : SkbId) (state : PacketState) (notCrypted : state ≠ .crypted)
    (history : List RxHistory.Event) : Preserves (Inv history) (setRxSkb id fun p => {p with state}) := by
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
      apply hi.transport_cells
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
      · intro before after hb ha _
        cases hd.symm.trans hb
        cases device.symm.trans ha
        exact Nat.le_refl _
      · intro pid after p ha hp
        cases device.symm.trans ha
        exact ⟨d,p,hd,hp,rfl⟩

/-- Concrete device updates that preserve packet cells, peer identity fields
and the allocation frontier are stable; other device fields may change. -/
theorem modifyDev_preserves (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (front : ∀ d, (f d).nextPeer = d.nextPeer)
    (packets : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (peers : ∀ (d : Device) (pid : PeerId), ((f d).peers[pid]?).map CurrentIdentity.identity =
      (d.peers[pid]?).map CurrentIdentity.identity)
    (history : List RxHistory.Event) : Preserves (Inv history) (modifyDev f) := by
  unfold modifyDev
  apply hoare_modify
  intro w hi
  apply hi.transport_cells
  · intro slot pkt cell _
    constructor
    · simpa only [RxDisposition.nativeRxStore,Option.bind_map,Function.comp_def,packets] using cell
    · simp [packetStamp,Option.map_map,Function.comp_def,epoch]
  · intro before after hb ha _
    have eq : after = f before := by simpa [hb] using ha.symm
    subst after
    rw [front]
    exact Nat.le_refl _
  · intro pid after p ha hp
    obtain ⟨before,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
    have old : (before.peers[pid]?).map CurrentIdentity.identity = some (CurrentIdentity.identity p) := by
      rw [← peers before pid,hp]
      rfl
    obtain ⟨q,hq,same⟩ := Option.map_eq_some_iff.mp old
    exact ⟨before,q,hb,hq,same.symm⟩

end Leanux.Proofs.WG.PublicationFrontier
