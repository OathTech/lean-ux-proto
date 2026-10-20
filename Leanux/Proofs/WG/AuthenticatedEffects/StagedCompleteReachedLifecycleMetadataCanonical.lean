import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigMetadataCanonical
import Leanux.Proofs.WG.RetirementSecurity.TxDestructSource

/-! Literal lifecycle helper witnesses retain each WG access, saved key-slot
write, rate-limiter update and original list/range prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

noncomputable def rangeShape (range : Std.Legacy.Range) (initial : σ)
    (body : Nat → σ → WG.M (ForInStep σ)) (shapes : ∀value acc,Shape (body value acc)) :
    Shape (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact listShape _ _ _ shapes

macro "lifecycle_metadata_step" : tactic => `(tactic| first
  | (metadata_source_head modify; apply Shape.access; apply Access.Shape.write; exact KeyFrames.world _ (fun _=>rfl))
  | (metadata_source_head ForIn.forIn; apply listShape)
  | (metadata_source_head ForIn.forIn; apply rangeShape)
  | unfold mayHaveSlept
  | metadata_source_step)

noncomputable def clearHandshakeShape (pid : PeerId) : Shape (handshakeClear pid) := by
  unfold handshakeClear
  repeat' first
    | (metadata_source_head handshakeZero; exact zeroShape _)
    | lifecycle_metadata_step

noncomputable def clearKeypairsShape (pid : PeerId) : Shape (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (metadata_source_head keypairPut; exact .access (Access.putShape _ _))
    | lifecycle_metadata_step

noncomputable def checkDestructShape : Shape TxWork.Destruct.check := by
  unfold TxWork.Destruct.check
  repeat' lifecycle_metadata_step

noncomputable def limiterInitShape : Shape ratelimiterInit := by
  unfold ratelimiterInit
  repeat' lifecycle_metadata_step

noncomputable def limiterGcShape (work : Bool) : Shape (gcEntries work) := by
  unfold gcEntries
  repeat' lifecycle_metadata_step

noncomputable def limiterUninitShape : Shape ratelimiterUninit := by
  unfold ratelimiterUninit
  repeat' first
    | (metadata_source_head gcEntries; exact limiterGcShape _)
    | lifecycle_metadata_step

noncomputable def settleDestructShape : Shape TxWork.Destruct.settle := by
  unfold TxWork.Destruct.settle
  repeat' first
    | (metadata_source_head ratelimiterUninit; exact limiterUninitShape)
    | lifecycle_metadata_step

noncomputable def cookieInitShape : Shape cookieCheckerInit := by
  unfold cookieCheckerInit
  repeat' lifecycle_metadata_step

noncomputable def pubkeyAllocShape : Shape pubkeyHashtableAlloc := by
  unfold pubkeyHashtableAlloc
  repeat' lifecycle_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
