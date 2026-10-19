import Leanux.Proofs.WG.RetirementSecurity.InvalidationFrames

/-! Rejection changes the rejected key direction at the C's original update.
TX requeue/handshake bookkeeping cannot undo it; release may remove the key.
RX rejection returns before AEAD and leaves its receiving direction invalid. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Invalidation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues CounterWindow Std.Do

def SendingInvalid (id : KeypairId) (w : WGWorld) : Prop :=
  ∀k,keyAt w id=some k→k.sending.isValid=false

def ReceivingInvalid (id : KeypairId) (w : WGWorld) : Prop :=
  ∀k,keyAt w id=some k→k.receiving.isValid=false

theorem sending_frame {id : KeypairId} {action : WG.M α} (same : SameView keyAt action) :
    Preserves (SendingInvalid id) action := same.wp (fun cells=>∀k,cells id=some k→k.sending.isValid=false)

theorem sending_put {id : KeypairId} (word : Option KeypairId) (now : Bool) :
    Preserves (SendingInvalid id) (keypairPut word now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  intro key found
  obtain ⟨old,resident,core⟩ := (put_retains word now w v a b run).keys id key found
  exact (congrArg (fun k=>k.sending.isValid) core).trans (before old resident)

def invalidateSending (id : KeypairId) : WG.M Unit := do
  let k←getKeypair id
  setKeypair id {k with sending:={k.sending with isValid:=false}}

def invalidateReceiving (id : KeypairId) : WG.M (Option RxPacket) := do
  let k←getKeypair id
  setKeypair id {k with receiving:={k.receiving with isValid:=false}}
  return none

theorem sending_update (id : KeypairId) : Hoare (invalidateSending id) (fun _=>True)
    (fun _=>SendingInvalid id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b _ run
  simp only [invalidateSending,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key,u,c,read,write⟩ := run
  obtain ⟨rfl,rfl,d,device,stored⟩ := KeyTimes.getKeypair_return id w u key a c read
  cases write
  intro final found
  simp [keyAt,device] at found
  cases found
  rfl

theorem receiving_update (id : KeypairId) : Hoare (invalidateReceiving id) (fun _=>True)
    (fun out w=>out=none ∧ ReceivingInvalid id w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b _ run
  simp only [invalidateReceiving,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key,u,c,read,ignored,t,e,write,done⟩ := run
  obtain ⟨rfl,rfl,d,device,stored⟩ := KeyTimes.getKeypair_return id w u key a c read
  cases write
  cases done
  refine ⟨rfl,?_⟩
  intro final found
  simp [keyAt,device] at found
  cases found
  rfl

theorem sending_rejection (pid : PeerId) (packets : List Packet) (id : KeypairId) :
    Hoare (stagedOutNokey pid packets (some id) true) (fun _=>True)
      (fun _=>SendingInvalid id) := by
  have tail : Preserves (SendingInvalid id) (do
      keypairPut (some id) false
      for _ in packets do _←branch .stagedOrphanWalk true
      _←branch .stagedOrphanWalk false
      setPeer pid {(←getPeer pid) with staged:=packets++(←getPeer pid).staged}
      sendQueuedHandshakeInitiation pid false) := by
    simp only [branch]
    repeat' first
      | (rx_retention_head keypairPut; exact sending_put _ _)
      | (rx_retention_head getPeer; exact sending_frame (peer_read _))
      | (rx_retention_head setPeer; exact sending_frame (peer_write _ _))
      | (rx_retention_head sendQueuedHandshakeInitiation; exact sending_frame (queuedHandshake _ _))
      | (rx_retention_head ForIn.forIn
         apply list_view_spec (fun w=>w) (SendingInvalid id)
         intro x acc
         change Preserves (SendingInvalid id) _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  simpa only [stagedOutNokey,invalidateSending,bind_assoc,Bool.true_eq,↓reduceIte] using
    hoare_bind _ _ (sending_update id) (fun _=>tail)

/-- The actual rejected branch factored from decryptPacket is exactly the
invalidating update, with no AEAD call in that branch. -/
theorem receiving_rejected (pkt : RxPacket) (w entered checked v : WGWorld)
    (a enteredAmbient checkedAmbient b : Ambient) (key : Keypair)
    (read : ((getKeypair pkt.keypair).run w).run (record a .decNoKeypair false)=
      .ok ((key,entered),enteredAmbient))
    (guard : ((KeyTimes.receiveReject key).run entered).run enteredAmbient=
      .ok ((true,checked),checkedAmbient))
    (run : ((decryptPacket pkt).run w).run a=.ok ((out,v),b)) :
    out=none ∧ ReceivingInvalid pkt.keypair v := by
  rw [KeyTimes.decryptPacket_factor] at run
  change ((do
      let k←getKeypair pkt.keypair
      let reject←KeyTimes.receiveReject k
      if reject then invalidateReceiving pkt.keypair else KeyTimes.receiveTail pkt k).run w).run
        (record a .decNoKeypair false)=.ok ((out,v),b) at run
  simp only [StateT.run_bind,read,CounterWindow.except_ok_bind,guard,ite_true] at run
  exact (hoare_iff_run_ambient _ _ _).mp (receiving_update pkt.keypair) checked checkedAmbient out v b True.intro run

end Leanux.Proofs.WG.RetirementSecurity.Invalidation
