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
  have ha := keypairAllocation_kernel_spec_sendBuffer_variant
    (fun k => sendWorkKernel k pid = (q, v))
  have hg := getPeer_sendWorkView pid q v
  have hp := setPeer_sendWorkView pid q v
  have h4 := fun e => send4_sendWorkView pid e bytes HANDSHAKE_DSCP true q v
  have h6 := fun e => send6_sendWorkView pid e bytes HANDSHAKE_DSCP true q v
  mvcgen [sendBufferToPeer, branch, invariant, ha, hg, hp, h4, h6]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sendWorkAt, sendWorkKernel, sendWorkDevice, workQueues, tableCursor, initiationAt, sendWorkPeer, initiationView, peerAt]

theorem sendBufferToPeer_spec_send_variant (pid : PeerId) (bytes : List UInt8)
    (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork (sendBufferToPeer pid bytes) pid
    (sendBufferToPeer_spec_sendWork_variant pid bytes) q v

theorem sendBufferToPeer_workView (pid : PeerId) (bytes : List UInt8) (v : WorkView) :
    ⦃fun w => ⌜workAt w pid = v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜workAt w pid = v⌝⦄ := by
  exact work_frame_of_sendWork (sendBufferToPeer pid bytes) pid
    (sendBufferToPeer_spec_sendWork_variant pid bytes) v

theorem sendBufferToPeer_queueWorkView (pid : PeerId) (bytes : List UInt8) (v : QueueWorkView) :
    ⦃fun w => ⌜queueWorkAt w pid = v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜queueWorkAt w pid = v⌝⦄ := by
  exact queueWork_frame_of_sendWork (sendBufferToPeer pid bytes) pid
    (sendBufferToPeer_spec_sendWork_variant pid bytes) v

theorem sendBufferToPeer_spec_initiation_variant (pid : PeerId) (bytes : List UInt8)
    (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send (sendBufferToPeer pid bytes) pid (sendBufferToPeer_spec_send_variant pid bytes) v

end Leanux.Proofs.WG.TimerDiscipline
