import Leanux.Proofs.WG.TransmitSecurity.BatchNativeAdmission

/-! Original create-data submission retains homogeneous queued batches on
success and both named queue refusals, including list cleanup after ENOSPC. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Offering (pid : PeerId) (slot : KeypairId) (items : List SkbId) (w : WGWorld) : Prop :=
  Inv w ∧ Aligned w pid slot items

theorem offering {action : WG.M α} (native : Preserves Inv action)
    (material : SameView PacketMaterial.view action) : Preserves (Offering pid slot items) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp native w a result v b before.1 run,
    before.2.frame ((ProjectedAction.iff_run_ambient _ _ _).mp material w a result v b run)⟩

theorem free_offering (id : SkbId) : Preserves (Offering pid slot items) (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (free_packet id) w a result v b before.1 run,?_⟩
  have packets := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.free_packet_wp id (TxDisposition.txPackets w)) w a result v b rfl run
  apply before.2.retains
  intro target packet resident
  rw [packets] at resident
  by_cases same : id = target
  · simp only [same,ite_true] at resident; cases resident
  · exact ⟨packet,by simpa only [same,ite_false] using resident,rfl⟩

theorem create_data (pid : PeerId) (slot : KeypairId) (items : List SkbId) :
    Preserves (Offering pid slot items) (createData pid items) := by
  let P := Offering pid slot items
  have enqueue : Preserves P (enqueuePerDeviceAndPeer pid items) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    exact Native.enqueue before.1 before.2 a b run
  have publish (state : PacketState) : Preserves P (enqueuePerPeerTx items state) :=
    offering (Native.publish items state) (PacketMaterial.publish items state)
  have packet (id : SkbId) : Preserves P (getTxSkb id) :=
    offering (read_packet id) (PacketMaterial.read_tx id)
  have peer (pid : PeerId) : Preserves P (getPeer pid) :=
    offering (read_peer pid) (PacketMaterial.read_peer pid)
  have payKey (kid : Option KeypairId) (now : Bool) : Preserves P (keypairPut kid now) :=
    offering (key_put kid now) (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid now))
  have payPeer (pid : Option PeerId) : Preserves P (peerPut pid) :=
    offering (peer_put pid) (PacketMaterial.of_packets (TxDisposition.peerPut_packets pid))
  have free (id : SkbId) : Preserves P (freeTxSkb id) := free_offering id
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  rxstack_preserves_source [createData,branch,invariant]
    using [enqueue,publish,packet,peer,payKey,payPeer,free,ambient,loop]

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
