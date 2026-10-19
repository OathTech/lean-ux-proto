import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEndpointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveLookup
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveObserved

/-! Paired receive finish uses its native lookup, the original counted
release observer, and the guarded statistics update. A final release may
settle tickets; no unconditional peer-release frame is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveFinish
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem after_lookup (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    Checked debts locals Safe
      (NestedPeerRelease.rxAfterLookupWith (Driver.nestedOps CausalJournal.hooks) pid ready routed) := by
  unfold NestedPeerRelease.rxAfterLookupWith
  apply bind_checked Safe (Disposal.original routed Safe accountSafe)
  intro ignored
  apply bind_checked Safe (Passive.ambient Safe accountSafe
    (AmbientM.branch .doneDishonestPeer (routed != some pid)))
  intro dishonest
  split
  · apply bind_checked Safe (Passive.native Safe accountSafe _ (ReceiveFrames.dishonest_frame .peer))
    intro ignored
    exact pure_checked Safe accountSafe none
  · apply bind_checked Safe (Passive.native Safe accountSafe _
      (ReceiveFrames.stats pid (ready.originalLen + MESSAGE_DATA_LEN_0)))
    intro ignored
    exact pure_checked Safe accountSafe (some (ready.bytes.take ready.ipLen))

/-- The complete actual receive-finish callback retains paired accounting
on normal and stopped paths, including the reached final-release settlement. -/
theorem checked (pid : PeerId) (ready : Packets.RxReady) :
    Checked debts locals Safe
      (NestedPeerRelease.rxFinishWith (Driver.nestedOps CausalJournal.hooks) pid ready) := by
  unfold NestedPeerRelease.rxFinishWith
  apply bind_checked Safe (Passive.native Safe accountSafe _
    (ReceiveLookup.frame ready.protocol ready.bytes))
  intro routed
  exact after_lookup Safe accountSafe pid ready routed

theorem endpoint (pid : PeerId) (e : Endpoint) :
    Checked debts locals Safe (liftWGPrefix (setPeerEndpoint pid e)) :=
  Passive.native Safe accountSafe _ (EndpointFrames.set pid e)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveFinish
