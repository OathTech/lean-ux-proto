import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt

/-! Native encryption ownership transport keeps the consumed alias explicit
across the actual softirq callback, then removes it only after its selected
continuation. Other active work remains disjoint throughout. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits OccurrenceStack

theorem tail_inventory (items : Option (List SkbId)) :
    Preserves (fun w : World => TxInventory locals w.wg)
      (RxWorkers.encryptStepTailSource items) := by
  let Q := fun w : WGWorld => TxInventory locals w
  let P := fun w : World => Q w.wg
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have readNative (id : SkbId) : Preserves Q (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    exact (Packets.getTxSkb_current id w v p a b run).1 ▸ before
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative id)
  have writeNative (id : SkbId) (bytes : List UInt8) :
      Preserves Q (setTxSkb id (fun p => {p with bytes})) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _ (setTx_holderStore id (fun p => {p with bytes}) (fun _ => rfl)))
      w a result v b run
    exact before.points same
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have publishNative (batch : List SkbId) (state : PacketState) :
      Preserves Q (enqueuePerPeerTx batch state) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.publish batch state a b run
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (publishNative batch state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact before.encrypt_packet key pkt run
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

theorem poll_points : SameView ownershipPointView TxRing.pollSource := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold TxRing.pollSource
  repeat' ownership_source_step initial

theorem poll (before : Ready locals active w) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a = .ok ((item,v),b)) :
    Ready locals (item.toList ++ active) v := by
  refine ⟨?_,before.2.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp poll_points w a item v b run),
    before.2.2.poll a b run⟩
  obtain ⟨history,allocation⟩ := before.1
  cases device : w.dev with
  | none => simp [TxRing.pollSource,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    simp [TxRing.pollSource,getDev,device,modifyDev] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    refine ⟨history,allocation.congr ?_ ?_⟩
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [device]
    · simp [allocationMetadata,deviceAllocationMetadata,device]

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncrypt
