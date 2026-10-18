import Leanux.Proofs.WG.TransmitSecurity.NonceCallerFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety

/-! Original keepalive and transmit callers carry the same allocation journal.
Only staging emits allocations; all caller prefixes and final peer payments
retain the original results, including Stop and its already reached history. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets

def keepaliveObserved (pid : PeerId) : WGPrefix Allocation Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .keepaliveStagedEmpty p.staged.isEmpty) then
    if ← liftWGPrefix (branch .keepaliveNoMem !(← liftWGPrefix (hiddenAlloc .keepaliveSkb))) then return
    liftWGPrefix (setPeer pid { p with staged := p.staged ++ [{ mtu := (← liftWGPrefix getDev).mtu }] })
  stagingObserved pid

theorem keepaliveObserved_erases (pid : PeerId) :
    ErasesStatePrefix (keepaliveObserved pid) (sendKeepalive pid) := by
  unfold keepaliveObserved sendKeepalive
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro empty
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro allocated
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro failed
    split
    · exact erasesStatePrefix_pure _
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro d
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      exact stagingObserved_erases _
  · exact stagingObserved_erases _

theorem keepaliveObserved_safe (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (keepaliveObserved pid) := by
  unfold keepaliveObserved
  repeat' first
    | (nonce_source_head stagingObserved; exact stagingObserved_safe _)
    | (nonce_source_head getPeer; exact Frames.lift_frame (Frames.peer_read _))
    | (nonce_source_head getDev; exact Frames.lift_frame Frames.device_read)
    | (nonce_source_head setPeer; exact Frames.lift_frame (Frames.peer_write _ _))
    | (nonce_source_head branch; exact Frames.lift_frame (Frames.ambient _))
    | (nonce_source_head hiddenAlloc; exact Frames.lift_frame (Frames.ambient _))
    | (nonce_source_head Pure.pure
       exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | split
    | (with_reducible intro x; try dsimp only)

def transmitObserved (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    WGPrefix Allocation Int := do
  match ← liftWGPrefix (txFront family addr packets mtu) with
  | .error err => pure err
  | .ok pid =>
    stagingObserved pid
    liftWGPrefix (peerPut (some pid))
    pure 0

theorem transmitObserved_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (transmitObserved family addr packets mtu) (wgXmit family addr packets mtu) := by
  rw [wgXmit_front_factor]
  unfold transmitObserved txTail
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro result
  cases result with
  | error err => exact erasesStatePrefix_pure _
  | ok pid => exact erasesStatePrefix_bind (stagingObserved_erases pid) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))

theorem transmitObserved_safe (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (transmitObserved family addr packets mtu) := by
  unfold transmitObserved
  apply StatePrefixEnsures.bind (Frames.lift_preserves (Frames.tx_front _ _ _ _))
  intro result
  cases result with
  | error err => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi)
  | ok pid =>
    apply StatePrefixEnsures.bind (stagingObserved_safe pid)
    intro _
    apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.peerPut _))
    intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
