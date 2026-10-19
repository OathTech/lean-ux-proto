import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionQueueFrames

/-! Reviewable native rejection postconditions. The two write witnesses are
actual ordered source cuts, not merely endpoint equations inferred from erasure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def Invalidated (kid : KeypairId) (before after : WGWorld) : Prop :=
  ∃ d key, before.dev = some d ∧ d.keypairs[kid]? = some key ∧
    after.dev = some {d with keypairs := d.keypairs.insert kid {key with sending := {key.sending with isValid := false}}}

def Restored (pid : PeerId) (packets : List Packet) (before after : WGWorld) : Prop :=
  ∃ d peer, before.dev = some d ∧ d.peers[pid]? = some peer ∧
    after.dev = some {d with peers := d.peers.insert pid {peer with staged := packets ++ peer.staged}}

theorem normal_effects (pid : PeerId) (packets : List Packet) (kid : KeypairId)
    (w v : WGWorld) (a b : Ambient)
    (run : ((stagedOutNokey pid packets (some kid) true).run w).run a = .ok (((),v),b)) :
    dropped v = dropped w ∧ ∃ first second : WGRunWitness Unit,
      first.before = w ∧ Invalidated kid first.before first.after ∧
      ((release kid packets).run first.after).run first.ambientAfter =
        .ok (((),second.before),second.ambientBefore) ∧
      Restored pid packets second.before second.after ∧
      ((sendQueuedHandshakeInitiation pid false).run second.after).run second.ambientAfter = .ok (((),v),b) ∧
      (runWGPrefix (observe pid packets kid) w a []).2 = [.invalidated kid first,.restored pid packets second] := by
  obtain ⟨first,second,entry,_,invalidated,released,restored,queued,events⟩ :=
    normal_receipts pid packets kid w v a b run
  obtain ⟨d,key,hd,hk,write,_⟩ := invalidation kid first invalidated
  obtain ⟨e,peer,he,hp,splice,_⟩ := restoration pid packets second restored
  exact ⟨(ProjectedAction.iff_run_ambient _ _ _).mp (rejected_dropped pid packets kid)
    w a () v b run,first,second,entry,⟨d,key,hd,hk,write⟩,released,⟨e,peer,he,hp,splice⟩,queued,events⟩

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
