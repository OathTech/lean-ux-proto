import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityBirth

/-! The native keepalive receipt introduces one fresh, available staged occurrence only
when allocation succeeds on an empty queue. Existing entries retain their
positions; an empty payload alone never establishes this origin. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal

theorem keepalive_inv (pid : PeerId) (r : WGRunWitness Bool)
    (valid : r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (before : Inv history r.before) :
    Inv (history ++ [.keepalivePrepared pid r]) r.after := by
  obtain ⟨d,p,device,resident,outcome⟩ := keepalive_prepare pid r valid
  rcases outcome with ⟨_,_,same⟩ | ⟨_,_,same⟩ | ⟨empty,ready,changed⟩
  · rw [same]; exact before.append (fun _ => by simp [Quiet,Uses])
  · rw [same]; exact before.append (fun _ => by simp [Quiet,Uses])
  · have epoch : Packets.epoch r.after = some d.ifindex := by
      simp [Packets.epoch,changed]
    have sameEpoch : Packets.epoch r.after = Packets.epoch r.before := by
      simp [Packets.epoch,changed,device]
    have slot : stagedAt r.after pid = some (p.internalId,[{mtu := d.mtu}]) := by
      simp [stagedAt,changed]
    apply before.changed [.keepalivePrepared pid r] (fun _ => by simp [Quiet,Uses]) sameEpoch epoch slot
    · intro q different
      simp [stagedAt,changed,device,Std.TreeMap.getElem?_insert,Ne.symm different]
    · refine ⟨[⟨history.length,0⟩],by simp,.cons ⟨?_,?_⟩ .nil⟩
      · exact Origins.Born.keepalive r history [] d.mtu rfl valid ready epoch
          (by simp [stagedAt,device,resident,empty]) slot (by simp [device])
      · exact Available.fresh (by simp [Quiet,Uses])

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
