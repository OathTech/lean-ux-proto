import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorSource

/-! Native write and read facts at the fixed queue boundaries. These frames
do not move logical tickets or assign births before their actual receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

def clock (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
  {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}

def queueWorld (pid : PeerId) (p : Peer) (packets : List Packet) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with staged := packets}}}

theorem peer_read (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((getPeer pid).run w).run a=.ok ((p,w),a) := by simp [getPeer,getDev,device,resident]

theorem take_read (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((takeRead pid).run w).run a=.ok (( (p,p.staged.isEmpty),w),clock a .stagedEmpty p.staged.isEmpty) := by
  simp [takeRead,getPeer,getDev,device,resident,branch,AmbientM.branch,clock]

theorem take_write (device : w.dev=some d) :
    ((takeWrite pid p).run w).run a=.ok (((),queueWorld pid p [] d w),a) := by
  simp [takeWrite,setPeer,modifyDev,device,queueWorld]

theorem restore_read (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((restoreRead pid).run w).run a=.ok (((p,p),w),a) := by
  simp [restoreRead,getPeer,getDev,device,resident]

theorem restore_write (device : w.dev=some d) :
    ((restoreWrite pid packets (p,p)).run w).run a=
      .ok (((),queueWorld pid p (packets++p.staged) d w),a) := by
  simp [restoreWrite,setPeer,modifyDev,device,queueWorld]

theorem keepalive_read (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((keepaliveRead pid).run w).run a=
      .ok (((p,p.staged.isEmpty),w),clock a .keepaliveStagedEmpty p.staged.isEmpty) := by
  simp [keepaliveRead,getPeer,getDev,device,resident,branch,AmbientM.branch,clock]

theorem keepalive_allocate (w : WGWorld) (a : Ambient) :
    ((keepaliveAllocate).run w).run a=
      (keepaliveAllocation.run a).map (fun (value,b)=>((value,w),b)) := by
  change (((StateT.lift (AmbientM.hiddenAlloc .keepaliveSkb) : WG.M Bool) >>= fun value =>
    StateT.lift (AmbientM.branch .keepaliveNoMem (!value))).run w).run a=_
  simp only [StateT.run_bind,stateLiftAmbient_run,keepaliveAllocation]
  cases native : (AmbientM.hiddenAlloc .keepaliveSkb).run a with
  | error stop => simp only [Except.map]; rfl
  | ok out =>
    obtain ⟨value,b⟩:=out
    simp only [Except.map]
    exact stateLiftAmbient_run (AmbientM.branch .keepaliveNoMem (!value)) w b

theorem keepalive_mtu (device : w.dev=some d) :
    ((keepaliveMtu).run w).run a=.ok ((d.mtu,w),a) := by simp [keepaliveMtu,getDev,device]

theorem keepalive_write (device : w.dev=some d) :
    ((keepaliveWrite pid p d.mtu).run w).run a=
      .ok (((),queueWorld pid p (p.staged++[{mtu:=d.mtu}]) d w),a) := by
  simp [keepaliveWrite,setPeer,modifyDev,device,queueWorld]

theorem queue_geometry (device : w.dev=some d) :
    Staged.stagedAt (queueWorld pid p packets d w) pid=some (p.internalId,packets) ∧
    Staged.dropped (queueWorld pid p packets d w)=Staged.dropped w ∧
    Packets.epoch (queueWorld pid p packets d w)=Packets.epoch w := by
  simp [queueWorld,Staged.stagedAt,Staged.dropped,Packets.epoch,device]

theorem queue_position (ordinal : Nat) (position : packets[ordinal]?=some packet) :
    (Staged.Obligations.stagedPackets d.ifindex pid p.internalId (queueWorld pid p packets d w))[ordinal]?=some packet := by
  simpa [Staged.Obligations.stagedPackets,queueWorld,Staged.stagedAt,Packets.epoch] using position

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
