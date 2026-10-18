import Leanux.Proofs.WG.Lifetimes.HandshakeReceive

/-! Original handshake queue consumption and complete bounded worker. Queue
bytes are values, not modeled resident skbs. Rescheduling remains an explicit
observed callback and can mutate residents subject to its ambient contract. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def popHandshakeQueue (ring : PtrRing (List UInt8 × SkbSource)) (d : Device) : Device :=
  {d with handshakeQueue := ring}

def decHandshakeQueue (d : Device) : Device :=
  {d with handshakeQueueLen := d.handshakeQueueLen - 1}

structure ReceiveQueueContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  pop : ∀ ring, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev (popHandshakeQueue ring)))
  decrement : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev decHandshakeQueue))

structure ProductReceiveQueueContracts (I : List LifetimeEvent → World → Prop) : Prop where
  pop : ∀ ring, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev (popHandshakeQueue ring))))
  decrement : PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev decHandshakeQueue)))

theorem ProductReceiveQueueContracts.ofNative (q : ReceiveQueueContracts I) :
    ProductReceiveQueueContracts (fun h w => I h w.wg) where
  pop := fun ring => (q.pop ring).liftWGObserver
  decrement := q.decrement.liftWGObserver

theorem allocationReceiveQueue : ReceiveQueueContracts AllocationInv := by
  constructor
  · intro ring
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [popHandshakeQueue, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, popHandshakeQueue,
        Option.map_map, Function.comp_def] <;> rfl
  ·
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [decHandshakeQueue, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata,
        decHandshakeQueue, Option.map_map, Function.comp_def] <;> rfl

def receiveStepPrefix : MixedM Bool := do
  match (← liftWGPrefix getDev).handshakeQueue.consume with
  | (none, _) => do
    _ ← liftWGPrefix (branch .workerConsumed false)
    return false
  | (some (msg, src), ring) =>
    _ ← liftWGPrefix (branch .workerConsumed true)
    liftWGPrefix (modifyDev (popHandshakeQueue ring))
    receiveHandshakePacketPrefix msg src
    liftWGPrefix (modifyDev decHandshakeQueue)
    return true

def receiveIterPrefix (afterItem : PrefixM LifetimeEvent Bool) : PrefixM LifetimeEvent IterResult :=
  workerIterPrefix .receiveWorker none (liftWGObserver receiveStepPrefix) afterItem

def handshakeReceiveWorkerPrefix (condResched : PrefixM LifetimeEvent Unit) : PrefixM LifetimeEvent Unit :=
  workerLoopPrefix .receiveWorker none (liftWGObserver receiveStepPrefix) condResched
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

theorem receiveStepPrefix_erases : ErasesStatePrefix receiveStepPrefix receiveStep := by
  unfold receiveStepPrefix receiveStep
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  rcases hc : d.handshakeQueue.consume with ⟨item, ring⟩
  cases item with
  | none => exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _)
  | some item =>
    rcases item with ⟨msg, src⟩
    exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
        erasesStatePrefix_bind (receiveHandshakePacketPrefix_erases msg src) (fun _ =>
          erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))))

theorem receiveIterPrefix_erases (hc : ErasesPrefix afterItem originalAfter) :
    ErasesPrefix (receiveIterPrefix afterItem)
      (workerIter .receiveWorker none receiveStep originalAfter) :=
  workerIterPrefix_erases _ _ (liftWGObserver_erases receiveStepPrefix_erases) hc

theorem handshakeReceiveWorkerPrefix_erases (hc : ErasesPrefix condResched originalResched) :
    ErasesPrefix (handshakeReceiveWorkerPrefix condResched)
      (handshakeReceiveWorker originalResched) :=
  workerLoopPrefix_erases _ _ (liftWGObserver_erases receiveStepPrefix_erases) hc _ _

theorem receiveStepPrefix_preserves (c : AmbientContracts I)
    (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe receiveStepPrefix := by
  have branch_spec (decision : Decision) (value : Bool) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (branch decision value)) :=
    AmbientContracts.drop (c.store (fun _ => True) _
      (by intro initial; exact hoare_liftAmbient (AmbientM.branch decision value) _))
  have done (b : Bool) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (pure b : MixedM Bool) := by
    exact StatePrefixEnsures.pure b (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  unfold receiveStepPrefix

  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) getDev getDev_sameWGStore))
  intro d
  rcases hc : d.handshakeQueue.consume with ⟨item, ring⟩
  cases item with
  | none =>

    exact StatePrefixEnsures.bind (branch_spec _ _) (fun _ => done false)
  | some item =>
    rcases item with ⟨msg, src⟩
    exact StatePrefixEnsures.bind (branch_spec _ _) (fun _ =>
      StatePrefixEnsures.bind (q.pop ring) (fun _ =>
        StatePrefixEnsures.bind (receiveHandshakePacketPrefix_preserves c r msg src) (fun _ =>
          StatePrefixEnsures.bind q.decrement (fun _ => done true))))

theorem receiveStepPrefix_preserves_product (c : ProductAmbientContracts I)
    (r : ProductHandshakeReceiveContracts I)
    (q : ProductReceiveQueueContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver receiveStepPrefix) := by
  have branch_spec (decision : Decision) (value : Bool) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (branch decision value))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (by intro initial; exact hoare_liftAmbient (AmbientM.branch decision value) _))
  have done (b : Bool) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (pure b : MixedM Bool)) := by
    rw [liftWGObserver_pure]
    exact PrefixPreserves.pure c.safe b
  unfold receiveStepPrefix
  rw [liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore))
  intro d
  rcases hc : d.handshakeQueue.consume with ⟨item, ring⟩
  cases item with
  | none =>
    rw [liftWGObserver_bind]
    exact PrefixPreserves.bind (branch_spec _ _) (fun _ => done false)
  | some item =>
    rcases item with ⟨msg, src⟩
    simp only [liftWGObserver_bind]
    apply PrefixPreserves.bind (branch_spec _ _)
    intro _
    apply PrefixPreserves.bind (q.pop ring)
    intro _
    apply PrefixPreserves.bind (receiveHandshakePacketPrefix_preserves_product c r msg src)
    intro _
    exact PrefixPreserves.bind q.decrement (fun _ => done true)

theorem receiveIterPrefix_preserves (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (q : ProductReceiveQueueContracts I) (hc : PrefixPreserves I LifetimeEvent.Safe afterItem) :
    PrefixPreserves I LifetimeEvent.Safe (receiveIterPrefix afterItem) :=
  workerIterPrefix_preserves _ _ c.safe (receiveStepPrefix_preserves_product c r q) hc

theorem handshakeReceiveWorkerPrefix_preserves (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (q : ProductReceiveQueueContracts I) (hc : PrefixPreserves I LifetimeEvent.Safe condResched) :
    PrefixPreserves I LifetimeEvent.Safe (handshakeReceiveWorkerPrefix condResched) :=
  workerLoopPrefix_preserves _ _ c.safe (receiveStepPrefix_preserves_product c r q) hc _ _

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

def original : (call : HandshakeReceiveCall) → WG.M call.Result
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

theorem erases (call : HandshakeReceiveCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | endpoint pid src => exact setPeerEndpointFromSkbPrefix_erases pid src
  | reply src bytes => exact sendBufferAsReplyToSkbPrefix_erases src bytes
  | cookie msg src => exact sendHandshakeCookiePrefix_erases msg src
  | packet msg src => exact receiveHandshakePacketPrefix_erases msg src
  | step => exact receiveStepPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (q : ReceiveQueueContracts I) (call : HandshakeReceiveCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | endpoint pid src => exact setPeerEndpointFromSkbPrefix_preserves c pid src
  | reply src bytes => exact sendBufferAsReplyToSkbPrefix_preserves c r.socket src bytes
  | cookie msg src => exact sendHandshakeCookiePrefix_preserves c r msg src
  | packet msg src => exact receiveHandshakePacketPrefix_preserves c r msg src
  | step => exact receiveStepPrefix_preserves c r q

theorem preserves_ambient_product (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (q : ProductReceiveQueueContracts I) (call : HandshakeReceiveCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | endpoint pid src => exact setPeerEndpointFromSkbPrefix_preserves_product c pid src
  | reply src bytes => exact sendBufferAsReplyToSkbPrefix_preserves_product c r.socket src bytes
  | cookie msg src => exact sendHandshakeCookiePrefix_preserves_product c r msg src
  | packet msg src => exact receiveHandshakePacketPrefix_preserves_product c r msg src
  | step => exact receiveStepPrefix_preserves_product c r q

theorem allocation (call : HandshakeReceiveCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationHandshakeReceive allocationReceiveQueue

end HandshakeReceiveCall
end Leanux.Proofs.WG.Lifetimes
