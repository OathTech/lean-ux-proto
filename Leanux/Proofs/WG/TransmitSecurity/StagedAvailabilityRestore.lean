import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHeldFrames

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

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
  simpa only [List.append_nil] using before.changed [] (fun _ _ member => by cases member) sameEpoch (sameEpoch ▸ epoch) slot
    (fun q different => by
      simp only [stagedAt,after,device,Option.bind_some,Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq,Ne.symm different,↓reduceIte])
    (batch.append (fun _ member => by cases member))


theorem held_restore (pid : PeerId) (peer : Peer) :
    StatePrefixEnsures (Held pid peer) Safe
      (liftWGPrefix (HandshakeSecurity.NonceRejection.restore pid peer.staged))
      (fun _ h w _ => Carrier h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  exact ⟨restore_origin pid peer ⟨value,w,v,a,b⟩ run before.1.1 before.2,before.1.2⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
