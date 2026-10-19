import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginFrames

/-! The worker writes only the ciphertext certified by its preceding native
encryption. The source condition is consumed at the actual byte update. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition
variable {id : SkbId}

def WriteSource (h : List WorkerEncryption.Receipt) (id : SkbId) (bytes : List UInt8)
    (w : WGWorld) : Prop :=
  ∀ generation, PacketOrigins.epoch w = some generation → ∀ packet,
    txPackets w id = some packet →
      Certificate h generation id (PacketPayload.material {packet with bytes})

theorem write_bytes (id : SkbId) (bytes : List UInt8) :
    Hoare (setTxSkb id (fun p => {p with bytes}))
      (fun w => Inv h w ∧ WriteSource h id bytes w) (fun _ => Inv h) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases device : w.dev with
  | none => simp [setTxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,packet,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setTxSkb_run w a d id p (fun p => {p with bytes}) device packet] at run
      cases run
      intro generation atEpoch target value resident nonempty
      have oldEpoch : PacketOrigins.epoch w = some generation := by
        simpa [PacketOrigins.epoch,Packets.update,device] using atEpoch
      by_cases same : id = target
      · subst target
        have valueEq : {p with bytes} = value := by
          simpa [txPackets,Packets.update,device] using resident
        subst value
        exact before.2 generation oldEpoch p (by simp [txPackets,device,packet])
      · exact before.1 generation oldEpoch target value
          (by simpa [txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,same] using resident) nonempty

theorem read_cell (r : RunWitness DataPacket) (valid : r.Valid (liftWG (getTxSkb id))) :
    r.after.wg = r.before.wg ∧ txPackets r.after.wg id = some r.value := by
  change (liftWG (getTxSkb id)).run r.before = .ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases native : ((getTxSkb id).run r.before.wg).run r.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok out =>
    obtain ⟨⟨packet,w⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,world⟩ := valid
    obtain ⟨kept,_,d,device,resident⟩ := Packets.getTxSkb_current id r.before.wg w packet r.before.ambient a native
    have worldEq : r.after.wg = w := congrArg World.wg world.symm
    refine ⟨worldEq.trans kept,?_⟩
    rw [worldEq,kept]
    simp [txPackets,device,resident,same]

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
