import Leanux.Proofs.WG.TransmitSecurity.StagedOriginFrames

/-! The native keepalive receipt introduces one fresh staged occurrence only
when allocation succeeds on an empty queue. Existing entries retain their
positions; an empty payload alone never establishes this origin. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal

theorem keepalive_inv (pid : PeerId) (r : WGRunWitness Bool)
    (valid : r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (before : Inv history r.before) :
    Inv (history ++ [.keepalivePrepared pid r]) r.after := by
  obtain ⟨d,p,device,resident,outcome⟩ := keepalive_prepare pid r valid
  rcases outcome with ⟨_,_,same⟩ | ⟨_,_,same⟩ | ⟨empty,ready,changed⟩
  · rw [same]; exact before.append _
  · rw [same]; exact before.append _
  · have epoch : Packets.epoch r.after = some d.ifindex := by
      simp [Packets.epoch,changed]
    have sameEpoch : Packets.epoch r.after = Packets.epoch r.before := by
      simp [Packets.epoch,changed,device]
    have slot : stagedAt r.after pid = some (p.internalId,[{mtu := d.mtu}]) := by
      simp [stagedAt,changed]
    apply before.changed [.keepalivePrepared pid r] sameEpoch epoch slot
    · intro q different
      simp [stagedAt,changed,device,Std.TreeMap.getElem?_insert,Ne.symm different]
    · exact keepalive_birth r valid ready epoch
        (by simp [stagedAt,device,resident,empty]) slot (by simp [device]) history

theorem keepalive_observed (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Carrier h w) Safe
      (AuthenticatedEffects.CausalJournal.keepalivePrepare pid) := by
  intro w a h before
  unfold AuthenticatedEffects.CausalJournal.keepalivePrepare
  have equation := runWGPrefix_receiptWGObserved
    (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (Event.keepalivePrepared pid) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : WGRunWitness Bool := ⟨value,w,v,a,b⟩
    have safe : Safe (h ++ [.keepalivePrepared pid receipt]) := before.2.emit True.intro
    exact ⟨[.keepalivePrepared pid receipt],rfl,safe,
      keepalive_inv pid receipt run before.1,safe⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
