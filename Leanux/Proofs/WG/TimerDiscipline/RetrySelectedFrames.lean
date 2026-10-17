import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpFrames
import Leanux.Proofs.WG.TimerDiscipline.FireSectionSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Normal completion of an explicitly selected retransmit unit above the retry
limit preserves the initially empty send queue. Outer wheel selection is separate. -/
theorem fireSelected_giveUp_empty (pid : PeerId) (we : WheelEntry) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Product.Ensures (fireWheelSelected .timerRetransmit pid .retransmitHandshake we)
      (fun w => w.wg.dev = some d)
      (fun _ w => w.wg.dev.map Device.sendWorkQueue = some []) := by
  let detached := FireReady.detachedPeer p
  let detachedDevice := withPeer d pid detached
  let P : WGWorld → Prop := fun g => g.dev = some detachedDevice
  let Q : WGWorld → Prop := fun g => g.dev.map Device.sendWorkQueue = some []
  have resident' : detachedDevice.peers[pid]? = some detached := by simp [detachedDevice, withPeer]
  have native : Ensures (expiredRetransmitHandshake pid) P (fun _ => Q) :=
    expiredRetransmit_giveUp_empty pid detachedDevice detached resident' empty limit
  have callback : Product.Ensures (liftWG (expiredRetransmitHandshake pid))
      (fun w => P w.wg) (fun _ w => Q w.wg) := by
    intro w result final pre run
    change (((expiredRetransmitHandshake pid).run w.wg).run w.ambient >>= fun ((value, g), a) =>
      .ok (value, {w with wg := g, ambient := a})) = _ at run
    cases actual : ((expiredRetransmitHandshake pid).run w.wg).run w.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, g⟩, a⟩ := pair
      rw [actual] at run
      cases run
      exact native w.wg w.ambient () g a pre actual
  have sectionContract : Product.Ensures
      (Env.runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid)))
      (fun w => P w.wg) (fun _ w => Q w.wg) :=
    (Product.ensures_iff _ _ _).mpr
      (runTimerSection_kernel_contract .timerRetransmit _
        (fun g _ _ _ => P g) (fun g _ _ _ => Q g)
        ((Product.ensures_iff _ _ _).mp callback))
  have deletion : Product.Ensures (liftWG (delTimer pid .retransmitHandshake))
      (fun w => w.wg.dev = some d) (fun _ w => P w.wg) := by
    intro w result final pre run
    rw [FireReady.detach w d p pid pre resident] at run
    cases run
    rfl
  have enter : Product.Ensures (modifyWG fun s => {s with timerPassStep := some we.bucketExpiry})
      (fun (w : World) => P w.wg) (fun _ (w : World) => P w.wg) := by
    intro w result final pre run
    cases run
    exact pre
  have leave : Product.Ensures (modifyWG fun s => {s with timerPassStep := none})
      (fun (w : World) => Q w.wg) (fun _ (w : World) => Q w.wg) := by
    intro w result final pre run
    cases run
    exact pre
  change Product.Ensures (do
    liftWG (delTimer pid .retransmitHandshake)
    modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
    Env.runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
    modifyWG fun s => {s with timerPassStep := none}) _ _
  refine Product.ensures_bind _ _ deletion ?_
  intro ignored
  refine Product.ensures_bind _ _ enter ?_
  intro ignored
  refine Product.ensures_bind _ _ sectionContract ?_
  intro ignored
  exact leave

end Leanux.Proofs.WG.TimerDiscipline
