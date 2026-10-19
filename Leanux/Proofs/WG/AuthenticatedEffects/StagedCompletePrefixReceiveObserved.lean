import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTimerQueue
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveObserved

/-! Receive maintenance carries Entry and terminal completeness on the same
ledger. Actual queued initiation retains its paired counted release contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive HandshakeSecurity.StagedDisposal
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List CausalJournal.Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

macro "prefix_receive_step " safe:term " using " accounted:term : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; apply Passive.native $safe $accounted; solve | entry_receive_native)
  | (maintenance_head Pure.pure; exact pure_checked $safe $accounted _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_intro
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | (maintenance_head ite; split))

theorem received (pid : PeerId) : Checked debts locals Safe (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ (TimerFrames.store getDev_sameWGStore))
  intro d
  apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branch .timersDataReceivedRunning d.running))
  intro running
  split
  · apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
    intro p
    apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branch .timersDataReceivedNotPending !(p.timerPending .sendKeepalive)))
    intro ready
    split
    · simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
      exact bind_checked Safe (Timer.modify_timer Safe accountSafe _ _ _ _) (fun _ => pure_checked Safe accountSafe ())
    · change Checked debts locals Safe (liftWGPrefix (getPeer pid) >>= fun p =>
        liftWGPrefix (setPeer pid {p with timerNeedAnotherKeepalive := true}))
      rw [← Queued.lift_bind]
      exact Passive.native Safe accountSafe _ (Queued.update pid
        (fun p => {p with timerNeedAnotherKeepalive := true}) (fun _ => ⟨rfl,rfl,rfl⟩))
  · exact pure_checked Safe accountSafe ()

theorem fresh (pid : PeerId) : Checked debts locals Safe
    (PacketSource.freshReceiveWith effects peerRelease pid) := by
  unfold PacketSource.freshReceiveWith
  apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
  intro first
  apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branch .rxFreshSentLastminute first.sentLastminuteHandshake))
  intro sent
  split
  · exact pure_checked Safe accountSafe ()
  · apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.read pid))
    intro peer
    apply bind_checked Safe (Passive.native Safe accountSafe _ (ReceiveFrames.fresh_decision peer.keypairCurrent))
    intro requested
    apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branch .rxFreshSend requested))
    intro send
    split
    · apply bind_checked Safe (Passive.native Safe accountSafe _ (Queued.update pid
        (fun p => {p with sentLastminuteHandshake := true}) (fun _ => ⟨rfl,rfl,rfl⟩)))
      intro ignored
      exact TimerQueue.queued Safe accountSafe pid false
    · exact pure_checked Safe accountSafe ()

theorem prepare (pid : PeerId) (pkt : RxPacket) : Checked debts locals Safe
    (PacketSource.prepareWith effects peerRelease pid pkt) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold PacketSource.prepareWith
  simp only [effects,CausalEffects.ops,TimerEffects.observed]
  repeat' first
    | (maintenance_head PacketSource.freshReceiveWith; exact fresh Safe accountSafe _)
    | (maintenance_head TimerEffects.traversalWith; exact Timer.traversal Safe accountSafe _)
    | (maintenance_head TimerEffects.dataReceivedWith; exact received Safe accountSafe _)
    | prefix_receive_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveObserved
