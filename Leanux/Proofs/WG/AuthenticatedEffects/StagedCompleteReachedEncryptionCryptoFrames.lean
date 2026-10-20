import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCryptoSource

/-! Quiet native frames before encryption's receipt. Native key reads and
scatter checks retain the full WG projection; histories remain unchanged
until the existing AEAD receipt is actually emitted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity EncryptionInterior EncryptionPrimitive

theorem prepared_same
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (value,u)) : u.wg=w.wg :=
  (preparationShape packet).normal prepared

theorem key_same
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (some value,u))
    (read : (liftWG (getKeypair slot)).run u=.ok (key,v)) : v.wg=w.wg :=
  ((ProjectedAction.iff_run _ _ _).mp (Primitive.key slot).frame u key v read).trans
    (prepared_same prepared)

theorem scatter_same
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (some value,u))
    (read : (liftWG (getKeypair slot)).run u=.ok (key,v))
    (checked : (branch .encSgvecFailed false : Leanux.M Bool).run v=.ok (failed,q)) : q.wg=w.wg :=
  ((ProjectedAction.iff_run _ _ _).mp (Primitive.ambient (branch .encSgvecFailed false)).frame
    v failed q checked).trans (key_same prepared read)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
