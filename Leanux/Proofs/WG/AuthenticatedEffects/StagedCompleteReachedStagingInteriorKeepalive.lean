import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorRestore

/-! The keepalive insertion has a fixed allocation-choice prefix. A stopped
choice retains the actual preceding read world; refusal is a normal false
return. The existing nonempty queue arm returns true without inserting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity CausalJournal RetirementSecurity
set_option maxHeartbeats 600000

theorem keepalive_insert (device : w.dev=some d) :
    ((keepaliveInsert pid p).run w).run a=
      .ok ((true,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w),a) := by
  unfold keepaliveInsert
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨d.mtu,w,a,keepalive_mtu device,?_⟩
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨(),_,_,keepalive_write device,rfl⟩

theorem keepalive_nonempty (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (nonempty : p.staged.isEmpty=false) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=
      .ok ((true,w),clock a .keepaliveStagedEmpty false) := by
  rw [keepalive_factor]
  simp only [StateT.run_bind,keepalive_read device resident,nonempty]
  rfl

theorem keepalive_allocated (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (refused,b)) :
    ((keepaliveAllocated pid).run w).run a=.ok (((p,some refused),w),b) := by
  unfold keepaliveAllocated
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨(p,true),w,clock a .keepaliveStagedEmpty true,?_,?_⟩
  · simpa only [empty] using keepalive_read (a:=a) device resident
  · simp only [ite_true]
    rw [MaterialOrigin.bind_ok_ambient]
    refine ⟨refused,w,b,?_,rfl⟩
    rw [keepalive_allocate,allocation]
    rfl

theorem keepalive_refused (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (true,b)) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.ok ((false,w),b) := by
  rw [keepalive_allocated_factor]
  simp only [StateT.run_bind,keepalive_allocated device resident empty allocation]
  rfl

theorem keepalive_inserted (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=
      .ok ((true,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w),b) := by
  rw [keepalive_allocated_factor,MaterialOrigin.bind_ok_ambient]
  exact ⟨(p,some false),w,b,keepalive_allocated device resident empty allocation,keepalive_insert device⟩

theorem keepalive_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.error stop := by
  unfold OccurrenceHandshake.keepalivePrepare
  simp only [StateT.run_bind,failed]
  rfl

theorem keepalive_allocation_stopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true)
    (failed : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.error stop) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.error stop := by
  rw [keepalive_factor]
  simp only [StateT.run_bind,keepalive_read device resident,empty]
  change ((keepaliveTail pid (p,true)).run w).run (clock a .keepaliveStagedEmpty true)=_
  unfold keepaliveTail
  simp only [ite_true,StateT.run_bind,keepalive_allocate,failed,Except.map]
  rfl

inductive KeepaliveCase (pid : PeerId) (w : WGWorld) (a : Ambient) :
    Except Stop ((Bool × WGWorld) × Ambient) → Prop where
  | readStopped (failed : ((getPeer pid).run w).run a=.error stop) : KeepaliveCase pid w a (.error stop)
  | nonempty (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (nonempty : p.staged.isEmpty=false) : KeepaliveCase pid w a
        (.ok ((true,w),clock a .keepaliveStagedEmpty false))
  | allocationStopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (empty : p.staged.isEmpty=true)
      (failed : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.error stop) :
      KeepaliveCase pid w a (.error stop)
  | refused (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true)
      (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (true,b)) :
      KeepaliveCase pid w a (.ok ((false,w),b))
  | inserted (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true)
      (allocation : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
      KeepaliveCase pid w a (.ok ((true,queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w),b))

theorem KeepaliveCase.literal (path : KeepaliveCase pid w a result) :
    ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=result := by
  cases path with
  | readStopped failed => exact keepalive_read_stopped failed
  | nonempty device resident nonempty => exact keepalive_nonempty device resident nonempty
  | allocationStopped device resident empty failed => exact keepalive_allocation_stopped device resident empty failed
  | refused device resident empty allocation => exact keepalive_refused device resident empty allocation
  | inserted device resident empty allocation => exact keepalive_inserted device resident empty allocation

theorem keepalive_cases (pid : PeerId) (w : WGWorld) (a : Ambient) :
    KeepaliveCase pid w a (((OccurrenceHandshake.keepalivePrepare pid).run w).run a) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop => rw [keepalive_read_stopped read]; exact .readStopped read
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v p a b read
    cases empty : p.staged.isEmpty with
    | false => rw [keepalive_nonempty device resident empty]; exact .nonempty device resident empty
    | true =>
      cases allocation : keepaliveAllocation.run (clock b .keepaliveStagedEmpty true) with
      | error stop => rw [keepalive_allocation_stopped device resident empty allocation]; exact .allocationStopped device resident empty allocation
      | ok out =>
        obtain ⟨refused,c⟩:=out
        cases refused with
        | true => rw [keepalive_refused device resident empty allocation]; exact .refused device resident empty allocation
        | false => rw [keepalive_inserted device resident empty allocation]; exact .inserted device resident empty allocation

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
