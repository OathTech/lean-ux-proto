import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialCursor
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeyFrames

/-! Conditional resident TX-key bindings. A certificate names the actual
packet allocation, its entry key core and the nonnull packet-peer owner at
that historical cut. Disposal may remove either object or clear an owner;
only surviving packet/key pairs create an obligation. Allocation arguments
and initialized shared-driver transport are proved separately. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder TxDisposition
variable {id : SkbId}

def Certificate (h : List Journal.Event) (generation id : Nat)
    (packet : DataPacket) (core : KeyCore) : Prop :=
  ∃ (packets : List DataPacket) (run : WGRunWitness (List SkbId)) (index : Nat) (input : DataPacket),
    Journal.Event.allocated packets run ∈ h ∧ run.Valid (packets.mapM newTxSkb) ∧
    PacketOrigins.epoch run.after = some generation ∧ packets[index]? = some input ∧
    run.value[index]? = some id ∧ PacketMaterial.material input = packet ∧
    pool run.before input.keypair = some core ∧
    RxCredits.keyWords run.before input.keypair = some (some input.peer)

def Inv (h : List Journal.Event) (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ id packet, d.txSkbs[id]? = some packet →
    packet.keypair < d.nextKeypairId ∧ ∃ core,
      Certificate h d.ifindex id (PacketMaterial.material packet) core ∧
      ∀ current, pool w packet.keypair = some current → current = core

theorem Certificate.mono (certificate : Certificate h generation id packet core)
    (included : h ⊆ later) : Certificate later generation id packet core := by
  obtain ⟨packets,run,index,input,member,rest⟩ := certificate
  exact ⟨packets,run,index,input,included member,rest⟩

theorem Certificate.origin (certificate : Certificate h generation id packet core) :
    PacketOrigins.Certificate h generation id packet := by
  obtain ⟨packets,run,index,input,member,valid,epoch,atInput,atId,material,_⟩ := certificate
  exact ⟨packets,run,member,valid,epoch,index,input,atInput,atId,material⟩

theorem Inv.mono (before : Inv h w) (included : h ⊆ later) : Inv later w := by
  intro d device id packet stored
  obtain ⟨bound,core,certificate,conditional⟩ := before d device id packet stored
  exact ⟨bound,core,certificate.mono included,conditional⟩

theorem empty (w : WGWorld) (packets : ∀ d, w.dev = some d → d.txSkbs = {}) : Inv h w := by
  intro d device id packet stored
  simp [packets d device] at stored

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  apply empty
  intro d device
  cases net <;> cases bare <;> simp [Runner.initialWG] at device <;>
    subst d <;> rfl

/-- Backward packet retention plus below-frontier key retention is sufficient.
Neither a key's existence nor the survival of a packet is assumed. -/
theorem Inv.retains (before : Inv h w) (packets : PacketOrigins.Retains w v)
    (frontier : ∀ d e, w.dev = some d → v.dev = some e → d.nextKeypairId ≤ e.nextKeypairId)
    (keys : ∀ d, w.dev = some d → ∀ slot, slot < d.nextKeypairId →
      ∀ core, pool v slot = some core → pool w slot = some core) : Inv h v := by
  intro after device id packet stored
  have cell : PacketMaterial.view v id = some (PacketMaterial.material packet) := by
    simp only [PacketMaterial.view,txPackets,device,Option.bind_some,stored,Option.map_some]
  obtain ⟨oldEpoch,oldCell⟩ := packets after.ifindex (by simp [PacketOrigins.epoch,device]) id _ cell
  obtain ⟨oldPacket,oldStored,material⟩ := Option.map_eq_some_iff.mp oldCell
  obtain ⟨prior,priorDevice,priorStored⟩ := Option.bind_eq_some_iff.mp oldStored
  have epoch : prior.ifindex = after.ifindex := by simpa [PacketOrigins.epoch,priorDevice] using oldEpoch
  have slot : oldPacket.keypair = packet.keypair :=
    by simpa only [PacketMaterial.material] using congrArg DataPacket.keypair material
  obtain ⟨bound,core,certificate,conditional⟩ := before prior priorDevice id oldPacket priorStored
  refine ⟨slot ▸ Nat.lt_of_lt_of_le bound (frontier prior after priorDevice device),core,?_,?_⟩
  · simpa only [epoch,material] using certificate
  · intro current resident
    apply conditional current
    apply keys prior priorDevice oldPacket.keypair bound current
    simpa only [slot] using resident

/-- Original session creation/derivation/rotation preserves every conditional
resident packet-to-key binding. The packet's carried frontier bound excludes
the fresh slot, including when the referenced older key was already absent. -/
theorem session (pid : PeerId) : Preserves (Inv h) (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains
  · exact PacketOrigins.Retains.of_snapshot ((ProjectedAction.iff_run_ambient _ _ _).mp
      (PacketOrigins.snapshot_wire (RetirementSecurity.OccurrenceKeys.session_wire pid))
      w a result v b run)
  · intro d e hd he
    exact session_cursor pid w v a b result hd he run
  · intro d hd slot bound core resident
    exact session_below pid w v a b result hd run slot bound core resident

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
