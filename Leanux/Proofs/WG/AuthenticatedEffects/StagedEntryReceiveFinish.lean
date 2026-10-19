import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourcePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEndpointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveLookup
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveObserved

/-! Actual receive finish uses its native lookup, the original counted
release observer, and the guarded statistics update. A final release may
settle tickets; no unconditional peer-release frame is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveFinish
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open SourcePassive
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem after_lookup (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    Checked debts locals Safe
      (NestedPeerRelease.rxAfterLookupWith (Driver.nestedOps CausalJournal.hooks) pid ready routed) := by
  unfold NestedPeerRelease.rxAfterLookupWith
  apply bind_checked Safe (Source.release routed Safe entrySafe)
  intro ignored
  apply bind_checked Safe (SourcePassive.ambient Safe entrySafe
    (AmbientM.branch .doneDishonestPeer (routed != some pid)))
  intro dishonest
  split
  · apply bind_checked Safe (SourcePassive.native Safe entrySafe _ (ReceiveFrames.dishonest_frame .peer))
    intro ignored
    exact pure_checked Safe entrySafe none
  · apply bind_checked Safe (SourcePassive.native Safe entrySafe _
      (ReceiveFrames.stats pid (ready.originalLen + MESSAGE_DATA_LEN_0)))
    intro ignored
    exact pure_checked Safe entrySafe (some (ready.bytes.take ready.ipLen))

/-- The complete actual receive-finish callback retains an accounted entry
on normal and stopped paths, including the reached final-release settlement. -/
theorem checked (pid : PeerId) (ready : Packets.RxReady) :
    Checked debts locals Safe
      (NestedPeerRelease.rxFinishWith (Driver.nestedOps CausalJournal.hooks) pid ready) := by
  unfold NestedPeerRelease.rxFinishWith
  apply bind_checked Safe (SourcePassive.native Safe entrySafe _
    (ReceiveLookup.frame ready.protocol ready.bytes))
  intro routed
  exact after_lookup Safe entrySafe pid ready routed

theorem endpoint (pid : PeerId) (e : Endpoint) :
    Checked debts locals Safe (liftWGPrefix (setPeerEndpoint pid e)) :=
  SourcePassive.native Safe entrySafe _ (EndpointFrames.set pid e)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveFinish
