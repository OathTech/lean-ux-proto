import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveFinish

/-! Receive completion retains paired accounting through confirmation-triggered
staging, actual maintenance and the source lookup/release suffix. Staging is
the one separately implemented callback required by this composition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveTail
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

def afterHandshake (pid : PeerId) (pkt : RxPacket) : WGPrefix Event (Option Key) := do
  match ← HandshakeSecurity.StagedDisposal.PacketSource.prepareWith effects peerRelease pid pkt with
  | none => pure none
  | some ready => NestedPeerRelease.rxFinishWith (Driver.nestedOps CausalJournal.hooks) pid ready

theorem after_handshake (pid : PeerId) (pkt : RxPacket) :
    Checked debts locals Safe (afterHandshake pid pkt) := by
  unfold afterHandshake
  apply bind_checked Safe (ReceiveObserved.prepare Safe accountSafe pid pkt)
  intro ready
  cases ready with
  | none => exact pure_checked Safe accountSafe none
  | some ready => exact ReceiveFinish.checked Safe accountSafe pid ready

theorem checked (pid : PeerId) (pkt : RxPacket) (confirmed : Bool)
    (staging : Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.receiveTailObserved CausalJournal.hooks pid pkt confirmed) := by
  unfold Driver.receiveTailObserved
  apply bind_checked Safe (Passive.ambient Safe accountSafe (AmbientM.branch .doneReceivedNew confirmed))
  intro promoted
  dsimp only
  split
  · exact bind_checked Safe (Passive.native Safe accountSafe _
      (TimerFrames.handshake_complete pid .walltimeLastHandshakeData)) (fun _ =>
        bind_checked Safe staging (fun _ => after_handshake Safe accountSafe pid pkt))
  · exact after_handshake Safe accountSafe pid pkt

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveTail
