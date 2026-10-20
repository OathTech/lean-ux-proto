import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveMetadataCanonical

/-! Metadata continuations lifted to a WG journal retain the original source
suffix. No journal event is produced by a native metadata action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged

noncomputable def prefixRemainder {E α : Type} {body : WG.M α} {source : Shape body}
    (point : Point source w a v b) : WGPrefix E α :=
  liftWGPrefix (Classical.choose point.remaining)

theorem prefixRemainder_run {E α : Type} {body : WG.M α} {source : Shape body}
    (point : Point source w a v b) (h : List E) :
    runWGPrefix (liftWGPrefix body) w a h = runWGPrefix (prefixRemainder point) v b h := by
  simpa only [prefixRemainder,runWGPrefix_lift] using
    congrArg (fun out => (out,h)) (Classical.choose_spec point.remaining)

theorem prefixRemainder_appends {E α : Type} {body : WG.M α} {source : Shape body}
    (point : Point source w a v b) : StateAppends (prefixRemainder (E:=E) point) :=
  StateAppends.lift _

noncomputable def decryptRejectShape (key : Keypair) : Shape (Lifetimes.decryptKeyReject key) := by
  unfold Lifetimes.decryptKeyReject
  repeat' receive_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
