import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical

/-! Receive metadata source trees expose actual reads, saved-peer writes and
ambient decisions. Their native points preserve the original continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def conditionalShape (test : Prop) [Decidable test] {left right : WG.M α}
    (yes : test → Shape left) (no : ¬test → Shape right) : Shape (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

macro "receive_metadata_step" : tactic => `(tactic| first
  | (metadata_source_head ite; apply conditionalShape)
  | metadata_source_step)

noncomputable def keyReadShape (kid : KeypairId) : Shape (getKeypair kid) := by
  repeat' metadata_source_step

noncomputable def peerReadShape (pid : PeerId) : Shape (getPeer pid) :=
  .access (readShape pid)

noncomputable def expiredShape (site : Decision) (birth : Int64) (limit : Nat) :
    Shape (branchExpired site birth limit) := by
  repeat' metadata_source_step

noncomputable def freshWriteShape (pid : PeerId) :
    Shape (do setPeer pid {(← getPeer pid) with sentLastminuteHandshake := true}) :=
  updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def previousShape (pid : PeerId) :
    Shape (do let p ← getPeer pid; setPeer pid {p with keypairPrevious := p.keypairCurrent}) :=
  updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def currentShape (pid : PeerId) (kid : KeypairId) :
    Shape (do let p ← getPeer pid; setPeer pid {p with keypairCurrent := some kid, keypairNext := none}) :=
  updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def statsPeerShape (pid : PeerId) (len : Nat) :
    Shape (do let p ← getPeer pid; setPeer pid {p with rxBytes := p.rxBytes + len}) :=
  updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def dishonestShape (why : Dishonest) : Shape (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' metadata_source_step

noncomputable def ecnShape (protocol ds : Nat) (bytes : List UInt8) :
    Shape (inetEcnDecapsulate protocol ds bytes) := by
  unfold inetEcnDecapsulate inetEcnSet ipEcnSetCe ipEcnSetEct1 ip6EcnSetCe ip6EcnSetEct1
  repeat' receive_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
