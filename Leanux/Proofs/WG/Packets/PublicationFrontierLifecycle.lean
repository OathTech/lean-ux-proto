import Leanux.Proofs.WG.Packets.PublicationFrontierCreation

/-! Vacant device populations discharge old packet obligations. The actual
setup reset and packet free are treated at their source endpoints; this does
not transport a certificate across an arbitrary epoch reset. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- An empty crypted population needs no historical certificate, regardless
of the previous device epoch or old journal contents. -/
theorem Inv.no_crypted (history : List RxHistory.Event) (w : WGWorld)
    (empty : ∀ d, w.dev = some d → ∀ (id : SkbId) (pkt : RxPacket),
      d.rxSkbs[id]? = some pkt → pkt.state ≠ .crypted) : Inv history w := by
  refine ⟨?_,PeersBelow.no_crypted w empty⟩
  apply PublicationHistory.Inv.no_crypted
  intro id pkt cell crypted
  obtain ⟨d,hd,hp⟩ := Option.bind_eq_some_iff.mp cell
  exact empty d hd id pkt hp crypted

theorem Inv.absent (history : List RxHistory.Event) (w : WGWorld) (hd : w.dev = none) :
    Inv history w := by
  apply Inv.no_crypted
  intro d resident
  simp [hd] at resident

/-- Actual wg_setup installs an empty RX store, even if the input fixture
already carried arbitrary peers, packets and a different frontier. -/
theorem wgSetup_establishes (history : List RxHistory.Event) :
    Hoare wgSetup (fun _ => True) (fun _ w => Inv history w) := by
  unfold wgSetup
  apply hoare_modify
  intro w _
  apply Inv.no_crypted
  intro d hd id pkt hp
  cases hd
  simp at hp

/-- Actual free retains every surviving packet, all resident peer identities,
and the epoch/frontier. The selected cell disappears; no reference premise is added. -/
theorem freeRxSkb_frame (id : SkbId) (w v : WGWorld) (a b : Ambient)
    (hr : ((freeRxSkb id).run w).run a = .ok (((),v),b)) :
    (∀ slot pkt, (RxDisposition.nativeRxStore v).2 slot = some pkt →
      (RxDisposition.nativeRxStore w).2 slot = some pkt) ∧
    (∀ slot, packetStamp v slot = packetStamp w slot) ∧
    CurrentIdentity.peerView v = CurrentIdentity.peerView w ∧ frontier v = frontier w := by
  cases hd : w.dev with
  | none => simp [freeRxSkb,liftSkb_run,hd] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,hd,hp,
        invariant,AmbientM.invariant] at hr
      cases hr
    | some pkt =>
      rw [Packets.freeRxSkb_run w a d id pkt hd hp] at hr
      cases hr
      have device : (Packets.update w (fun d => {d with rxSkbs := d.rxSkbs.erase id})).dev =
          some {d with rxSkbs := d.rxSkbs.erase id} := by simp [Packets.update,hd]
      refine ⟨?_,?_,?_,?_⟩
      · intro slot packet cell
        have selected : (d.rxSkbs.erase id)[slot]? = some packet := by
          simpa [RxDisposition.nativeRxStore,device] using cell
        have surviving : d.rxSkbs[slot]? = some packet := by
          by_cases same : id = slot
          · subst slot; simp at selected
          · simpa [Std.TreeMap.getElem?_erase,same] using selected
        simp [RxDisposition.nativeRxStore,hd,surviving]
      · intro slot; simp [packetStamp,device,hd]
      · simp [CurrentIdentity.peerView,device,hd]
      · simp [frontier,device,hd]

end Leanux.Proofs.WG.PublicationFrontier

namespace Leanux.Proofs.WG.PublicationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- Packet completion needs only the old anchor invariant. It does not
require the allocation-frontier bound used by future peer creation. -/
theorem freeRxSkb_preserves (id : SkbId) (history : List RxHistory.Event) :
    Preserves (Inv history) (freeRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  obtain ⟨packets,stamps,peers,_⟩ := PublicationFrontier.freeRxSkb_frame id w v a b hr
  apply hi.transport
  · intro slot pkt cell _
    exact ⟨packets slot pkt cell,stamps slot⟩
  · intro pid d p hd hp
    have stored : (CurrentIdentity.peerView w).bind (fun cells => cells pid) =
        some (CurrentIdentity.identity p) := by
      rw [← peers]
      simp [CurrentIdentity.peerView,hd,hp]
    obtain ⟨before,hbefore,identity⟩ := Option.bind_eq_some_iff.mp stored
    obtain ⟨old,ho,fields⟩ := Option.map_eq_some_iff.mp hbefore
    subst before
    obtain ⟨q,hq,same⟩ := Option.map_eq_some_iff.mp identity
    exact ⟨old,q,ho,hq,same.symm⟩

end Leanux.Proofs.WG.PublicationHistory

namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- Freeing a packet removes only that obligation. Surviving packets retain
their exact stamp, bytes, peer identity and frontier, with no key-validity premise. -/
theorem freeRxSkb_preserves (id : SkbId) (history : List RxHistory.Event) :
    Preserves (Inv history) (freeRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (PublicationHistory.freeRxSkb_preserves id history)
    w a () v b hi.1 hr,?_⟩
  obtain ⟨packets,_,_,same⟩ := freeRxSkb_frame id w v a b hr
  intro after ha slot pkt cell crypted
  have final : (RxDisposition.nativeRxStore v).2 slot = some pkt := by
    simp [RxDisposition.nativeRxStore,ha,cell]
  have old : (w.dev.bind fun d => d.rxSkbs[slot]?) = some pkt := packets slot pkt final
  obtain ⟨before,hb,hpkt⟩ := Option.bind_eq_some_iff.mp old
  have fields : (after.ifindex,after.nextPeer) = (before.ifindex,before.nextPeer) := by
    simpa [frontier,ha,hb] using same
  have next : after.nextPeer = before.nextPeer := congrArg Prod.snd fields
  rw [next]
  exact hi.2 before hb slot pkt hpkt crypted

end Leanux.Proofs.WG.PublicationFrontier
