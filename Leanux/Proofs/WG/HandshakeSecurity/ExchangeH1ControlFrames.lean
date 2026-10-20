import Leanux.Proofs.WG.HandshakeSecurity.ExchangeScheduler

/-! Explicit per-call C2 H1 control projections at `be8c209c`. Clearing a
handshake permits zero, but cannot restore an earlier nonzero exchange tag. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

structure H1ControlTagFrames : Prop where
  /-- C2 `Noise.handshakeClear_tagMap_projected`, pin `be8c209c`, projected
  to surviving nonzero tags. -/
  clear : ∀ pid, H1TagRetains (handshakeClear pid)
  /-- C2 `Noise.DriverTags.Flush.keys_tags`, pin `be8c209c`. -/
  clearKeys : ∀ pid, H1TagSame (keypairsClear pid)
  /-- C2 `Noise.DriverTags.Silent.timerCallback_retained`, pin `be8c209c`. -/
  timer : ∀ pid timer, H1TagRetains (timerCallback pid timer)
  /-- C2 `Noise.DriverTags.Removal.makeDead_tags`, pin `be8c209c`. -/
  makeDead : ∀ pid, H1TagSame (peerMakeDead pid)
  /-- C2 `Noise.DriverTags.free_frame`, pin `be8c209c`. -/
  free : H1TagSame WG.free

end Leanux.Proofs.WG.HandshakeSecurity
