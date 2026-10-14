import Leanux.Proofs.WG.Lifetimes.HandshakeReceive

/-! Original handshake queue consumption and complete bounded worker. Queue
bytes are values, not modeled resident skbs. Rescheduling remains an explicit
observed callback and can mutate residents subject to its ambient contract. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def popHandshakeQueue (d : Device) : Device :=
  {d with handshakeQueue := d.handshakeQueue.drop 1}

def decHandshakeQueue (d : Device) : Device :=
  {d with handshakeQueueLen := d.handshakeQueueLen - 1}

structure ReceiveQueueContracts (I : List LifetimeEvent → World → Prop) : Prop where
  pop : PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev popHandshakeQueue))
  decrement : PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev decHandshakeQueue))

theorem allocationReceiveQueue : ReceiveQueueContracts AllocationInv := by
  constructor
  all_goals
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [popHandshakeQueue, decHandshakeQueue, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, popHandshakeQueue,
        decHandshakeQueue, Option.map_map, Function.comp_def] <;> rfl

def receiveStepPrefix : MixedM Bool := do
  match (← liftPrefix getDev).handshakeQueue with
  | [] => do
    _ ← liftPrefix (branch .workerConsumed false)
    return false
  | (msg, src) :: _ =>
    _ ← liftPrefix (branch .workerConsumed true)
    liftPrefix (modifyDev popHandshakeQueue)
    receiveHandshakePacketPrefix msg src
    liftPrefix (modifyDev decHandshakeQueue)
    return true

def receiveIterPrefix (afterItem : MixedM Bool) : MixedM IterResult :=
  workerIterPrefix .receiveWorker none receiveStepPrefix afterItem

def handshakeReceiveWorkerPrefix (condResched : MixedM Unit) : MixedM Unit :=
  workerLoopPrefix .receiveWorker none receiveStepPrefix condResched
    MAX_QUEUED_INCOMING_HANDSHAKES "the handshake queue did not drain"

theorem receiveStepPrefix_erases : ErasesPrefix receiveStepPrefix receiveStep := by
  unfold receiveStepPrefix receiveStep
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro d
  cases d.handshakeQueue with
  | nil => exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
  | cons item rest =>
    rcases item with ⟨msg, src⟩
    exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
        erasesPrefix_bind (receiveHandshakePacketPrefix_erases msg src) (fun _ =>
          erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _))))

theorem receiveIterPrefix_erases (hc : ErasesPrefix afterItem originalAfter) :
    ErasesPrefix (receiveIterPrefix afterItem)
      (workerIter .receiveWorker none receiveStep originalAfter) :=
  workerIterPrefix_erases _ _ receiveStepPrefix_erases hc

theorem handshakeReceiveWorkerPrefix_erases (hc : ErasesPrefix condResched originalResched) :
    ErasesPrefix (handshakeReceiveWorkerPrefix condResched)
      (handshakeReceiveWorker originalResched) :=
  workerLoopPrefix_erases _ _ receiveStepPrefix_erases hc _ _

theorem receiveStepPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) : PrefixPreserves I LifetimeEvent.Safe receiveStepPrefix := by
  unfold receiveStepPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel))
  intro d
  cases d.handshakeQueue with
  | nil =>
    exact PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      (fun _ => PrefixPreserves.pure c.safe _)
  | cons item rest =>
    rcases item with ⟨msg, src⟩
    exact PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _)) (fun _ =>
      PrefixPreserves.bind q.pop (fun _ =>
        PrefixPreserves.bind (receiveHandshakePacketPrefix_preserves c r msg src) (fun _ =>
          PrefixPreserves.bind q.decrement (fun _ => PrefixPreserves.pure c.safe _))))

theorem receiveIterPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) (hc : PrefixPreserves I LifetimeEvent.Safe afterItem) :
    PrefixPreserves I LifetimeEvent.Safe (receiveIterPrefix afterItem) :=
  workerIterPrefix_preserves _ _ c.safe (receiveStepPrefix_preserves c r q) hc

theorem handshakeReceiveWorkerPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) (hc : PrefixPreserves I LifetimeEvent.Safe condResched) :
    PrefixPreserves I LifetimeEvent.Safe (handshakeReceiveWorkerPrefix condResched) :=
  workerLoopPrefix_preserves _ _ c.safe (receiveStepPrefix_preserves c r q) hc _ _

/-- A finite family with its original result type, distinct from the
callback-parametric worker and scheduler iteration. -/
inductive HandshakeReceiveCall where
  | endpoint (pid : PeerId) (src : SkbSource)
  | reply (src : SkbSource) (bytes : List UInt8)
  | cookie (msg : List UInt8) (src : SkbSource)
  | packet (msg : List UInt8) (src : SkbSource)
  | step

namespace HandshakeReceiveCall

def Result : HandshakeReceiveCall → Type
  | .step => Bool
  | _ => Unit

def original : (call : HandshakeReceiveCall) → M call.Result
  | .endpoint pid src => setPeerEndpointFromSkb pid src
  | .reply src bytes => sendBufferAsReplyToSkb src bytes
  | .cookie msg src => sendHandshakeCookie msg src
  | .packet msg src => receiveHandshakePacket msg src
  | .step => receiveStep

def observed : (call : HandshakeReceiveCall) → MixedM call.Result
  | .endpoint pid src => setPeerEndpointFromSkbPrefix pid src
  | .reply src bytes => sendBufferAsReplyToSkbPrefix src bytes
  | .cookie msg src => sendHandshakeCookiePrefix msg src
  | .packet msg src => receiveHandshakePacketPrefix msg src
  | .step => receiveStepPrefix

theorem erases (call : HandshakeReceiveCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | endpoint pid src => exact setPeerEndpointFromSkbPrefix_erases pid src
  | reply src bytes => exact sendBufferAsReplyToSkbPrefix_erases src bytes
  | cookie msg src => exact sendHandshakeCookiePrefix_erases msg src
  | packet msg src => exact receiveHandshakePacketPrefix_erases msg src
  | step => exact receiveStepPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) (call : HandshakeReceiveCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | endpoint pid src => exact setPeerEndpointFromSkbPrefix_preserves c pid src
  | reply src bytes => exact sendBufferAsReplyToSkbPrefix_preserves c r.socket src bytes
  | cookie msg src => exact sendHandshakeCookiePrefix_preserves c r msg src
  | packet msg src => exact receiveHandshakePacketPrefix_preserves c r msg src
  | step => exact receiveStepPrefix_preserves c r q

theorem allocation (call : HandshakeReceiveCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationHandshakeReceive allocationReceiveQueue

end HandshakeReceiveCall
end Leanux.Proofs.WG.Lifetimes
