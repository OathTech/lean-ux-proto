import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsProjection

/-! Dependency-light native restoration and callback source. The witness and
historical material facts live in separate modules above the shared driver. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

def nativeRestore (pid : PeerId) (packets : List Packet) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}

def noKeyWith [Monad m] (o : TimerEffects.Ops m)
    (restore : PeerId → List Packet → m Unit) (queue : PeerId → Bool → m Unit)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) : m Unit := do
  if invalid then
    let some id := keypair | o.step (invariant "unreachable")
    let k ← o.step (getKeypair id)
    o.step (setKeypair id {k with sending := {k.sending with isValid := false}})
  o.step (keypairPut keypair false)
  for _ in packets do _ ← o.step (branch .stagedOrphanWalk true)
  _ ← o.step (branch .stagedOrphanWalk false)
  restore pid packets
  queue pid false


theorem core_native_factor [Monad m] (o : TimerEffects.Ops m)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    noKeyWith o (fun pid packets => o.step (nativeRestore pid packets))
      (TimerEffects.queuedWith o) pid packets keypair invalid =
      PacketEffects.noKeyWith o pid packets keypair invalid := rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
