import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialBounds
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverWorkerFrames

/-! Forgetting the extra authorization component of existing native frames.
The existential list below is merely a finite inventory of resident key
labels. It is not an execution history and asserts no confirmation event. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem bounds_inventory (hi : Bounds w) : ∃ labels, DriverCuts.Carrier labels w := by
  cases device : w.dev with
  | none =>
    refine ⟨[],hi.1,?_,hi.2⟩
    intro pid core resident _
    simp only [current,device] at resident
    cases resident
  | some d =>
    refine ⟨d.keypairs.toList.map (fun entry => entry.2.internalId),hi.1,?_,hi.2⟩
    intro pid core resident _
    simp only [current,device] at resident
    change (d.peers[pid]?.bind fun peer => peer.keypairCurrent.bind
      fun kid => (d.keypairs[kid]?).map keyCore) = some core at resident
    obtain ⟨peer,_,rest⟩ := Option.bind_eq_some_iff.mp resident
    obtain ⟨kid,_,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨key,stored,eq⟩ := Option.map_eq_some_iff.mp rest
    subst core
    exact List.mem_map.mpr ⟨(kid,key),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr stored,rfl⟩

theorem bounds_iff_inventory : Bounds w ↔ ∃ labels, DriverCuts.Carrier labels w :=
  ⟨bounds_inventory,fun ⟨_,hi⟩ => ⟨hi.1,hi.2.2⟩⟩

/-- Uniform native frames can forget their auxiliary finite label list.
No label is interpreted as an actual prior confirmation by this result. -/
theorem bounds_forget {action : WG.M α}
    (frame : ∀ labels, Preserves (DriverCuts.Carrier labels) action) : Preserves Bounds action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨labels,inventory⟩ := bounds_inventory hi
  have after := (hoare_iff_run_ambient _ _ _).mp (frame labels) w a result v b inventory run
  exact ⟨after.1,after.2.2⟩

theorem bounds_forget_product {action : Leanux.M α}
    (frame : ∀ labels, Preserves (fun w : World => DriverCuts.Carrier labels w.wg) action) :
    Preserves (fun w : World => Bounds w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨labels,inventory⟩ := bounds_inventory hi
  have after := (hoare_iff_run _ _ _).mp (frame labels) w result v inventory run
  exact ⟨after.1,after.2.2⟩

theorem bounds_peer_get (pid : PeerId) : Preserves Bounds (peerGet pid) :=
  bounds_forget (DriverCuts.carrier_peer_get pid)

theorem bounds_peer_put (pid : Option PeerId) : Preserves Bounds (peerPut pid) :=
  bounds_forget (DriverCuts.carrier_peer_put pid)

theorem bounds_key_put (kid : Option KeypairId) (now : Bool) : Preserves Bounds (keypairPut kid now) :=
  bounds_forget (DriverCuts.carrier_key_put kid now)

theorem bounds_read_peer (pid : PeerId) : Preserves Bounds (getPeer pid) :=
  bounds_forget (DriverCuts.carrier_read_peer pid)

theorem bounds_read_key (kid : KeypairId) : Preserves Bounds (getKeypair kid) :=
  bounds_forget (DriverCuts.carrier_key_read kid)

theorem bounds_skb (action : SkbM α) : Preserves Bounds (liftSkb action) :=
  bounds_forget (DriverCuts.carrier_skb action)

theorem bounds_update (pid : PeerId) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (identity : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    Preserves Bounds (do let p ← getPeer pid; setPeer pid (f p)) :=
  bounds_forget (DriverCuts.carrier_update pid f slots identity)

theorem bounds_confirmation (pid : PeerId) (kid : KeypairId) :
    Preserves Bounds (receivedWithKeypair pid kid) :=
  bounds_frame
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.receivedWithKeypair_view) pid kid)
    (CurrentSlots.receivedWithKeypair_preserves pid kid)

theorem bounds_endpoint (pid : PeerId) (ep : Endpoint) : Preserves Bounds (setPeerEndpoint pid ep) :=
  bounds_forget (DriverCuts.carrier_endpoint pid ep)

theorem bounds_complete (pid : PeerId) (site : HiddenSite) :
    Preserves Bounds (timersHandshakeComplete pid site) :=
  bounds_forget (DriverCuts.carrier_complete pid site)

theorem bounds_prepare (pid : PeerId) (pkt : RxPacket) : Preserves Bounds (RxCredits.prepareRest pid pkt) :=
  bounds_forget (DriverCuts.carrier_prepare pid pkt)

theorem bounds_finish (pid : PeerId) (ready : Packets.RxReady) : Preserves Bounds (Packets.rxFinish pid ready) :=
  bounds_forget (DriverCuts.carrier_finish pid ready)

theorem bounds_encrypt (item : Option (List SkbId)) :
    Preserves (fun w : World => Bounds w.wg) (RxWorkers.encryptStepTailSource item) :=
  bounds_forget_product (DriverCuts.carrier_encrypt_tail item)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
