import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial

/-! Establishing material certificates at the original packet allocator.
The caller must supply its actual admitted packet/key relation; arbitrary
allocation arguments do not establish cryptographic authorization. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder TxDisposition

def allocationView (w : WGWorld) := (pool w,cursor w,PacketOrigins.epoch w)

theorem skb_allocation_view (action : SkbM α) : SameView allocationView (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store hi device
  change ((fun kid => (d.keypairs[kid]?).map keyCore),some d.nextKeypairId,some d.ifindex) = initial
  change ((fun kid => (w.dev.bind fun dev => dev.keypairs[kid]?).map keyCore),
    w.dev.map (·.nextKeypairId),w.dev.map (·.ifindex)) = initial at hi
  rw [device] at hi
  exact hi

theorem allocation_view (packets : List DataPacket) :
    SameView allocationView (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec allocationView (· = initial)
  intro packet
  exact (skb_allocation_view (SkbStore.newTx packet)).wp (· = initial)

def Inputs (packets : List DataPacket) (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ packet ∈ packets,
    packet.keypair < d.nextKeypairId ∧ ∃ core, pool w packet.keypair = some core

/-- The actual native allocator installs each admitted packet with a
certificate tied to its entry key core. Older surviving cells retain their
certificates even on arbitrary occupied packet-slot inputs. -/
theorem allocated (packets : List DataPacket) (r : WGRunWitness (List SkbId))
    (valid : r.Valid (packets.mapM newTxSkb)) (before : Inv h r.before)
    (inputs : Inputs packets r.before) : Inv (h ++ [.allocated packets r]) r.after := by
  rcases r with ⟨item,w,v,a,b⟩
  change Inv h w at before
  change Inputs packets w at inputs
  change Inv (h ++ [.allocated packets ⟨item,w,v,a,b⟩]) v
  change ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b) at valid
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (allocation_view packets) w a item v b valid
  have cores : pool v = pool w := congrArg Prod.fst same
  have cursors : cursor v = cursor w := congrArg (fun f => f.2.1) same
  intro e after id packet stored
  change v.dev = some e at after
  cases device : w.dev with
  | none =>
    have noDevice : cursor v = none := by simpa [cursor,device] using cursors
    simp [cursor,after] at noDevice
  | some d =>
    have front : e.nextKeypairId = d.nextKeypairId := by
      simpa [cursor,device,after] using cursors
    have epochs : e.ifindex = d.ifindex := by
      have epoch : PacketOrigins.epoch v = PacketOrigins.epoch w := congrArg (fun f => f.2.2) same
      simpa [PacketOrigins.epoch,device,after] using epoch
    have resident : txPackets v id = some packet := by simp [txPackets,after,stored]
    rcases PacketOrigins.allocation_origin packets device valid id packet resident with old | fresh
    · have oldStored : d.txSkbs[id]? = some packet := by simpa [txPackets,device] using old
      obtain ⟨bound,core,certificate,conditional⟩ := before d device id packet oldStored
      refine ⟨by simpa only [front] using bound,core,?_,?_⟩
      · rw [epochs]
        exact certificate.mono (by intro x member; exact List.mem_append_left _ member)
      · intro current atKey
        exact conditional current (by simpa only [cores] using atKey)
    · obtain ⟨index,atPacket,atId⟩ := fresh
      obtain ⟨bound,core,atKey⟩ := inputs d device packet (List.mem_of_getElem? atPacket)
      refine ⟨by simpa only [front] using bound,core,?_,?_⟩
      · exact ⟨packets,⟨item,w,v,a,b⟩,index,packet,by simp,valid,
          by simp [PacketOrigins.epoch,after],atPacket,atId,rfl,atKey⟩
      · intro current resident
        exact Option.some.inj ((by simpa only [cores] using resident : pool w packet.keypair = some current).symm.trans atKey)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
