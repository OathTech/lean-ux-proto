import Leanux.Proofs.WG.TransmitSecurity.StagedSelectionOrigins

/-! The no-key arm restores the saved native batch into its empty queue.
Its original ticket sequence survives unchanged and is not counted as a new
birth, encryption, socket delivery or drop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem restore_origin (pid : PeerId) (peer : Peer) (r : WGRunWitness Unit)
    (valid : r.Valid (HandshakeSecurity.NonceRejection.restore pid peer.staged))
    (before : Inv history r.before) (saved : Saved history pid peer r.before) :
    Inv history r.after := by
  obtain ⟨generation,epoch,empty,batch⟩ := saved
  obtain ⟨d,p,device,resident,after,_⟩ :=
    HandshakeSecurity.NonceRejection.restoration pid peer.staged r valid
  have fields : p.internalId = peer.internalId ∧ p.staged = [] := by
    simpa only [stagedAt,device,Option.bind_some,resident,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] using empty
  have sameEpoch : Packets.epoch r.after = Packets.epoch r.before := by
    simp only [Packets.epoch,after,device,Option.map_some]
  have slot : stagedAt r.after pid = some (peer.internalId,peer.staged) := by
    simp [stagedAt,after,fields]
  simpa only [List.append_nil] using before.changed [] sameEpoch (sameEpoch ▸ epoch) slot
    (fun q different => by
      simp only [stagedAt,after,device,Option.bind_some,Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq,Ne.symm different,↓reduceIte])
    (batch.append_history [])

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
