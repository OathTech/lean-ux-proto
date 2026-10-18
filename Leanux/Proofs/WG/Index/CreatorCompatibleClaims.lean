import Leanux.Proofs.WG.Index.CreatorSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- All normal creator returns preserve the weaker compatible state. Early
refusals may retain NULL words; any inserted owner is justified by its actual
dereference. No successful-creation or readiness premise is supplied. -/
theorem createInitiation_owner_compatible (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid) (View.HandshakeCompatibleSafe pid)
      (fun _ => View.HandshakeCompatibleSafe pid) := by
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HandshakeCompatible pid d
  have write (f : Peer → Peer)
      (word : ∀p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
      (count : ∀p, (f p).refcount = p.refcount) :
      Ensures (modifyPeer pid f) P (fun _ => P) :=
    modifyPeer_device_predicate pid (HandshakeCompatible pid) f
      (fun d p resident pre => peerWrite_handshakeCompatible pid d p (f p)
        resident (word p) (count p) pre)
  exact createInitiation_preserves_source pid P
    (fun _ _ => write _ (fun _ => rfl) (fun _ => rfl))
    (fun _ => write _ (fun _ => rfl) (fun _ => rfl))
    (write _ (fun _ => rfl) (fun _ => rfl)) (creatorPublish_handshakeCompatible pid)

/-- All normal creator returns preserve the weaker compatible state. Early
refusals may retain NULL words; any inserted owner is justified by its actual
dereference. No successful-creation or readiness premise is supplied. -/
theorem createResponse_owner_compatible (pid : PeerId) :
    Campaign2.Ensures (createResponse pid) (View.HandshakeCompatibleSafe pid)
      (fun _ => View.HandshakeCompatibleSafe pid) := by
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HandshakeCompatible pid d
  have write (f : Peer → Peer)
      (word : ∀p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
      (count : ∀p, (f p).refcount = p.refcount) :
      Ensures (modifyPeer pid f) P (fun _ => P) :=
    modifyPeer_device_predicate pid (HandshakeCompatible pid) f
      (fun d p resident pre => peerWrite_handshakeCompatible pid d p (f p)
        resident (word p) (count p) pre)
  exact createResponse_preserves_source pid P
    (fun _ _ => write _ (fun _ => rfl) (fun _ => rfl))
    (fun _ => write _ (fun _ => rfl) (fun _ => rfl))
    (write _ (fun _ => rfl) (fun _ => rfl)) (creatorPublish_handshakeCompatible pid)

end Leanux.Proofs.WG.Index
