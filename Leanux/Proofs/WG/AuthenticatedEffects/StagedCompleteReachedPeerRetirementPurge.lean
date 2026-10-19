import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementCases

/-! The actual purge has two writes: charge the original length, then clear
that same cached peer's staged queue. Failure is confined to its initial
read; the charge-before-clear interval remains an explicit native prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
set_option maxHeartbeats 600000

theorem purge_charge_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((purgeChargeTo pid).run w).run a=.ok ((p,charged p d w),a) := by
  unfold purgeChargeTo
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨p,w,a,by simp [getPeer,getDev,device,resident],?_⟩
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨_,_,_,charge_run device,rfl⟩

theorem purge_clear_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((purgeStagedPackets pid).run w).run a=.ok (((),cleared pid p d w),a) := by
  rw [purge_factor,MaterialOrigin.bind_ok_ambient]
  exact ⟨_,_,_,purge_charge_prefix device resident,clear_run⟩

theorem purge_continuation (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((purgeStagedPackets pid).run w).run a=
      ((purgeClear pid p).run (charged p d w)).run a := by
  rw [purge_clear_prefix device resident,clear_run]

theorem purge_failed (failed : ((purgeStagedPackets pid).run w).run a=.error stop) :
    ((getPeer pid).run w).run a=.error stop := by
  cases read : ((getPeer pid).run w).run a with
  | error reason =>
    unfold purgeStagedPackets at failed
    simp only [StateT.run_bind,read] at failed
    cases failed
    rfl
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v p a b read
    rw [purge_clear_prefix device resident] at failed
    cases failed

/-- The actual whole native outcome always supplies its source read or both
literal mutation cuts; it never supplies a fabricated failed world. -/
theorem purge_cases (pid : PeerId) (w : WGWorld) (a : Ambient) :
    (∃ stop, ((getPeer pid).run w).run a=.error stop ∧
      ((purgeStagedPackets pid).run w).run a=.error stop) ∨
    (∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧
      ((purgeChargeTo pid).run w).run a=.ok ((p,charged p d w),a) ∧
      ((purgeStagedPackets pid).run w).run a=.ok (((),cleared pid p d w),a)) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop =>
    refine Or.inl ⟨stop,rfl,?_⟩
    unfold purgeStagedPackets
    simp only [StateT.run_bind,read]
    rfl
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v p a b read
    exact Or.inr ⟨d,p,device,resident,purge_charge_prefix device resident,purge_clear_prefix device resident⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
