import Leanux.Proofs.WG.TimerDiscipline.SendSocketFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Socket sending preserves the optional table/cursor and initiation observations
while updating endpoint-cache and accounting fields. These observations contain
fields not in campaign 1's keypair snapshot. -/
theorem sendBufferToPeer_spec_sendWork_variant (pid : PeerId) (bytes : List UInt8)
    (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    ambient (AmbientM.branch site value)
  have hget : Ensures (getPeer pid) P (fun _ => P) := by
    intro g input result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g input result final after pre run).1
  have haccount : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + bytes.length}) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
    intro p
    exact (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v _)
  have h4 (e : Endpoint) : Ensures (send4 e (some pid) bytes HANDSHAKE_DSCP true) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (send4_sendWorkView pid e bytes HANDSHAKE_DSCP true q v)
  have h6 (e : Endpoint) : Ensures (send6 e (some pid) bytes HANDSHAKE_DSCP true) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (send6_sendWorkView pid e bytes HANDSHAKE_DSCP true q v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes P (fun _ => P)) (noFrame : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold sendBufferToPeer
  repeat' first
    | exact hpure _
    | exact ambient _
    | exact hbranch _ _
    | exact hget
    | exact haccount
    | exact h4 _
    | exact h6 _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

theorem sendBufferToPeer_spec_send_variant (pid : PeerId) (bytes : List UInt8)
    (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (sendBufferToPeer pid bytes) pid
    (sendBufferToPeer_spec_sendWork_variant pid bytes) q v

theorem sendBufferToPeer_workView (pid : PeerId) (bytes : List UInt8) (v : WorkView) :
    ⦃fun w => ⌜workAt w pid = v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜workAt w pid = v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (sendBufferToPeer_spec_sendWork_variant pid bytes (sendWorkAt g pid).1 (sendWorkAt g pid).2)
    g ambient result final after rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map (fun q => q.2.1.1), x.2.map (fun p => p.2.1))) h
  have same : workAt final pid = workAt g pid := by
    simpa [workAt, workKernel, sendWorkAt, sendWorkKernel, sendWorkDevice, workQueues,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem sendBufferToPeer_queueWorkView (pid : PeerId) (bytes : List UInt8) (v : QueueWorkView) :
    ⦃fun w => ⌜queueWorkAt w pid = v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜queueWorkAt w pid = v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (sendBufferToPeer_spec_sendWork_variant pid bytes (sendWorkAt g pid).1 (sendWorkAt g pid).2)
    g ambient result final after rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map (fun q => q.2.1), x.2.map (fun p => p.2.1))) h
  have same : queueWorkAt final pid = queueWorkAt g pid := by
    simpa [queueWorkAt, queueWorkKernel, sendWorkAt, sendWorkKernel, sendWorkDevice,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem sendBufferToPeer_spec_initiation_variant (pid : PeerId) (bytes : List UInt8)
    (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (sendBufferToPeer pid bytes) pid (sendBufferToPeer_spec_send_variant pid bytes) v

end Leanux.Proofs.WG.TimerDiscipline
