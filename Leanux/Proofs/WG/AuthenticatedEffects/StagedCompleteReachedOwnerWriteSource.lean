import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical

/-! Owner-word writes expose the actual peer read or key access tree. The
handshake setter is one world write; its return is the post-write cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OwnerWrite
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def peerReadShape (pid : PeerId) : Access.Shape (getPeer pid) := by
  simp only [getPeer,getDev,invariant]
  repeat' access_source_step

noncomputable def keyShape (kid : KeypairId) (peer : Option PeerId) : Access.Shape ((IndexOwner.keypair kid).setPeerWord peer) := by
  simp only [IndexOwner.setPeerWord,getKeypair,getDev,setKeypair,invariant]
  repeat' access_source_step

inductive Point : IndexOwner → Option PeerId → WGWorld → Ambient → WGWorld → Ambient → Prop where
  | handshake (point : Access.Point (peerReadShape pid) w a v b) : Point (.handshake pid) peer w a v b
  | keypair (point : Access.Point (keyShape kid peer) w a v b) : Point (.keypair kid) peer w a v b
  | returned (performed : ((owner.setPeerWord peer).run w).run a=.ok (((),v),b)) : Point owner peer w a v b

theorem Point.remaining (point : Point owner peer w a v b) :
    ∃remaining : WG.M Unit,((owner.setPeerWord peer).run w).run a=(remaining.run v).run b := by
  cases point with
  | @handshake pid w a v b peer point=>
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest >>= fun p=>setPeer pid {p with handshakeEntryPeer:=peer},?_⟩
      simp only [IndexOwner.setPeerWord,StateT.run_bind,same]
  | keypair point=>exact point.remaining
  | returned performed=>exact ⟨pure (),performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OwnerWrite
