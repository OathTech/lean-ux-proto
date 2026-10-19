import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductFrames

/-! The environment deletion's literal guards and notification prefix are
separated from its observed destructor without changing native order or Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000

abbrev notifyDown : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
abbrev notifyUnregister : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister

def prefixObserved : PrefixM Event Unit := do
  if (←liftPrefix (liftWG getDev)).running then
    liftWGObserver (Driver.downObserved hooks)
    liftPrefix notifyDown
  liftPrefix (skipCut allocCuts)
  liftPrefix notifyUnregister
  liftPrefix (liftWG mayHaveSlept)

private theorem lift_bind (body : Leanux.M α) (next : α→Leanux.M β) :
    (liftPrefix (body >>= next) : PrefixM Event β)=
      (liftPrefix body >>= fun x=>liftPrefix (next x)) := by
  funext w h
  change ((body >>= next).run w,h)=runPrefix (liftPrefix body >>= fun x=>liftPrefix (next x)) w h
  rw [runPrefix_bind,runPrefix_lift]
  cases run : body.run w <;> simp only [StateT.run_bind,run,runPrefix_lift] <;> rfl

private theorem lift_pure (x : α) : (liftPrefix (pure x : Leanux.M α) : PrefixM Event α)=pure x := rfl

private theorem lift_ite (p : Prop) [Decidable p] (a b : Leanux.M α) :
    (liftPrefix (if p then a else b) : PrefixM Event α)=
      (if p then liftPrefix a else liftPrefix b) := by split <;> rfl

/-- The actual idle/dump guards run before the absent-device return; the
observed shutdown and destructor retain their original source positions. -/
theorem source_factor : Driver.envDeleteObserved hooks=(do
    liftPrefix HolderDeviceDelete.guards
    if (←liftPrefix getWG).dev.isNone then return -ENODEV
    prefixObserved
    liftWGObserver (Driver.destructObserved hooks)
    pure 0) := by
  unfold Driver.envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  unfold prefixObserved notifyDown notifyUnregister
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister
  simp only [HolderDeviceDelete.guards,lift_bind,lift_pure,lift_ite,bind_assoc,bind_if_source,pure_bind]
  rfl

theorem prefix_erases : ErasesPrefix prefixObserved Lifecycle.deletePrefix := by
  unfold prefixObserved Lifecycle.deletePrefix
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro d
  split <;> repeat' first
    | exact erasesPrefix_lift _
    | apply erasesPrefix_bind (liftWGObserver_erases CompleteNative.down_erases); intro _
    | apply erasesPrefix_bind (erasesPrefix_lift _); intro _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
