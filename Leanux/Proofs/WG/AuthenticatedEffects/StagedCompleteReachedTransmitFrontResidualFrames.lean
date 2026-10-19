import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualSource

/-! Native mutation geometry at the two overflow writes and the single splice
write. No endpoint accounting invariant is asserted between a mutation and
its later observed receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity CausalJournal
set_option maxHeartbeats 600000

def clock (a : Ambient) (excess : Bool) : Ambient :=
  {a with steps := a.steps.push {decision := .xmitStagedTrimIter, outcome := excess,netRx := a.netRxSection}}

def droppedWorld (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with staged := p.staged.drop 1}}}

def chargedWorld (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with staged := p.staged.drop 1}, txDropped := d.txDropped+1}}

def splicedWorld (pid : PeerId) (p : Peer) (packets : List Packet) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with staged := p.staged++packets}}}

theorem gate_run (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((gate pid).run w).run a=
      .ok (((p,decide (p.staged.length>MAX_STAGED_PACKETS)),w),
        clock a (decide (p.staged.length>MAX_STAGED_PACKETS))) := by
  simp [gate,getPeer,getDev,device,resident,branch,AmbientM.branch,clock]

theorem drop_run (device : w.dev=some d) :
    ((drop pid p).run w).run a=.ok (((),droppedWorld pid p d w),a) := by
  simp [drop,setPeer,modifyDev,device,droppedWorld]

theorem charge_run :
    (charge.run (droppedWorld pid p d w)).run a=.ok (((),chargedWorld pid p d w),a) := rfl

/-- Between removal and charge the old counter has not yet changed. -/
theorem drop_geometry (device : w.dev=some d) :
    Staged.stagedAt (droppedWorld pid p d w) pid=some (p.internalId,p.staged.drop 1) ∧
    Staged.dropped (droppedWorld pid p d w)=Staged.dropped w := by
  simp [droppedWorld,Staged.stagedAt,Staged.dropped,device]

theorem charged_geometry :
    Staged.stagedAt (chargedWorld pid p d w) pid=some (p.internalId,p.staged.drop 1) ∧
    Staged.dropped (chargedWorld pid p d w)=some (d.txDropped+1) := by
  simp [chargedWorld,Staged.stagedAt,Staged.dropped]

theorem body_run (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((Staged.trimBody pid).run w).run a=
      if p.staged.length>MAX_STAGED_PACKETS then
        .ok ((.yield (),chargedWorld pid p d w),clock a true)
      else .ok ((.done (),w),clock a false) := by
  rw [body_factor]
  simp only [StateT.run_bind,gate_run device resident]
  by_cases excess : p.staged.length>MAX_STAGED_PACKETS
  · simp [excess,drop,setPeer,modifyDev,charge,device,chargedWorld]
  · simp [excess]

/-- The splice reads return the same resident peer; the actual native update
appends every packet position, including repeated equal payloads. -/
theorem splice_run (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((xmitSplice pid packets).run w).run a=
      .ok (((),splicedWorld pid p packets d w),a) := by
  simp [xmitSplice,getPeer,getDev,device,resident,setPeer,modifyDev,splicedWorld]

theorem splice_geometry (device : w.dev=some d) :
    Staged.stagedAt (splicedWorld pid p packets d w) pid=some (p.internalId,p.staged++packets) ∧
    Staged.dropped (splicedWorld pid p packets d w)=Staged.dropped w := by
  simp [splicedWorld,Staged.stagedAt,Staged.dropped,device]

/-- A yielded iteration has passed the real guard and both writes. -/
theorem body_yield
    (run : ((Staged.trimBody pid).run w).run a=.ok ((.yield (),v),b)) :
    ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧ p.staged.length>MAX_STAGED_PACKETS ∧
      v=chargedWorld pid p d w ∧ b=clock a true := by
  have actual:=run
  unfold Staged.trimBody at actual
  rw [MaterialOrigin.bind_ok_ambient] at actual
  obtain ⟨p,u,c,read,_⟩:=actual
  obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w u p a c read
  rw [body_run device resident] at run
  split at run
  · cases run
    exact ⟨d,p,device,resident,by assumption,rfl,rfl⟩
  · cases run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
