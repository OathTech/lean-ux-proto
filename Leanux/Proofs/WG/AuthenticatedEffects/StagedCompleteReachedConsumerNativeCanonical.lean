import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLookupFrames

/-! Authentication fronts and accepted continuations expose fixed native accesses and read-derived metadata writes. The known successful initiation return cannot enter repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits.HandshakeLoans

noncomputable def precomputedShape (ck key : Key) : Shape (mixPrecomputedDh ck key) := by
  unfold mixPrecomputedDh
  repeat' metadata_source_step

noncomputable def decryptShape (sealed key hash : Key) : Shape (messageDecrypt sealed key hash) := by
  unfold messageDecrypt
  repeat' metadata_source_step

noncomputable def authFrontShape (msg : Key) : Shape (initiationAuthFront msg) := by
  unfold initiationAuthFront messageDecrypt
  repeat' metadata_source_step

noncomputable def cookieAuthShape (msg : Key) (pid : PeerId) : Shape (cookieAuthFront msg pid) := by
  unfold cookieAuthFront
  repeat' metadata_source_step

theorem out_some_source (peer : Option PeerId) (pid : PeerId) : initiationOut peer (some pid)=
    (do let _←branch .consumeFailedPut false;pure (some pid) : WG.M (Option PeerId)) := by
  rfl

noncomputable def outSomeShape (peer : Option PeerId) (pid : PeerId) : Shape (initiationOut peer (some pid)) := by
  rw [out_some_source]
  repeat' metadata_source_step

noncomputable def acceptedInitiationShape (msg : Key) (accepted : Option AcceptedInitiation) : Shape (initiationAcceptedContinue msg accepted) := by
  cases accepted with
  | none=>exact .access (.pure _)
  | some accepted=>
    unfold initiationAcceptedContinue initiationAcceptedFinish
    repeat' first
      | (metadata_source_head initiationOut; exact outSomeShape _ _)
      | metadata_source_step

noncomputable def acceptedResponseShape (msg : Key) (accepted : Option AcceptedResponse) : Shape (responseAcceptedContinue msg accepted) := by
  cases accepted with
  | none=>exact .access (.pure _)
  | some accepted=>
    unfold responseAcceptedContinue responseAcceptedFinish
    repeat' metadata_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata

