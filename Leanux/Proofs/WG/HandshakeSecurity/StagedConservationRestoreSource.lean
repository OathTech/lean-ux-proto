import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsProjection

/-! The same no-key source with the whole-batch restoration exposed before
handshake queueing. All rejection arms use this one cut; restoration is neither
a new packet birth nor a disposal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

structure Receipt where
  pid : PeerId
  packets : List Packet
  run : WGRunWitness Unit

def Receipt.Valid (r : Receipt) : Prop := r.run.Valid (NonceRejection.restore r.pid r.packets)

def observed (record : Receipt → E) (pid : PeerId) (packets : List Packet) : WGPrefix E Unit :=
  receiptWGObserved (liftWGPrefix (NonceRejection.restore pid packets)) (fun run => record ⟨pid,packets,run⟩)

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

theorem native_factor [Monad m] (o : TimerEffects.Ops m)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    noKeyWith o (fun pid packets => o.step (NonceRejection.restore pid packets))
      (TimerEffects.queuedWith o) pid packets keypair invalid =
      PacketEffects.noKeyWith o pid packets keypair invalid := rfl

theorem observed_erases (record : Receipt → E) (pid : PeerId) (packets : List Packet) :
    ErasesStatePrefix (observed record pid packets) (NonceRejection.restore pid packets) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem observed_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none) (pid : PeerId) (packets : List Packet) :
    StateProjectsPrefix ρ id (observed record pid packets)
      (liftWGPrefix (NonceRejection.restore pid packets)) :=
  Exchange.receipt_ignored ρ _ _ _
    (Exchange.quiet_native_projection ρ _ _ (erasesStatePrefix_lift _) (fun _ _ _ => rfl))
    (fun _ => quiet _)

theorem observed_completed (record : Receipt → E) (pid : PeerId) (packets : List Packet)
    (w v : WGWorld) (a b : Ambient) (h : List E)
    (run : ((NonceRejection.restore pid packets).run w).run a = .ok (((),v),b)) :
    runWGPrefix (observed record pid packets) w a h =
      (.ok (((),v),b),h ++ [record ⟨pid,packets,⟨(),w,v,a,b⟩⟩]) := by
  rw [observed,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

/-- The full native batch is returned at the head of the resident queue;
its actual disposal counter is unchanged. -/
theorem Receipt.Valid.effects (r : Receipt) (valid : r.Valid) :
    ∃ d peer, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧
      r.run.after.dev = some {d with peers := d.peers.insert r.pid {peer with staged := r.packets ++ peer.staged}} ∧
      NonceRejection.dropped r.run.after = NonceRejection.dropped r.run.before :=
  NonceRejection.restoration r.pid r.packets r.run valid

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
