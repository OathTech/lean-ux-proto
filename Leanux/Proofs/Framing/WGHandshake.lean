import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Handshake

/-! Canonical native-WG frames for the original access-free Noise helpers.
Their branches and record failures are unchanged. These frames alone do not
establish call coverage; callers inspect and observe every store access. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem generatePublic_sameWGWorld (secret : Key) :
    SameView (id : WGWorld → WGWorld) (generatePublic secret) := by
  apply SameView.of_wp
  intro k
  unfold generatePublic
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .genPublicNullSecret _) (fun w => w = k))
  intro b
  split <;> exact preserves_pure _

theorem kdf_sameWGWorld (second third : Bool) (chainingKey data : List UInt8) :
    SameView (id : WGWorld → WGWorld) (kdf second third chainingKey data) := by
  have hb (d : Decision) (b : Bool) : SameView (id : WGWorld → WGWorld) (branch d b) :=
    fun k => hoare_liftAmbient (AmbientM.branch d b) (fun w => w = k)
  have hor (a b : WG.M Bool) (ha : SameView (id : WGWorld → WGWorld) a)
      (hb : SameView (id : WGWorld → WGWorld) b) :
      SameView (id : WGWorld → WGWorld) (WG.orM a b) := by
    unfold WG.orM
    apply SameView.bind ha
    intro yes
    split
    · exact SameView.pure _ _
    · exact hb
  unfold kdf
  apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
  intro first
  split
  · exact SameView.pure _ _
  · apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
    intro second
    split
    · exact SameView.pure _ _
    · apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
      intro third
      split <;> exact SameView.pure _ _

theorem kdfOut_sameWGWorld (outs : List (List UInt8)) (i : Nat) :
    SameView (id : WGWorld → WGWorld) (kdfOut outs i) := by
  unfold kdfOut
  split
  · exact SameView.pure _ _
  · exact fun k => hoare_liftAmbient (AmbientM.invariant _) (fun w => w = k)

theorem messageEphemeral_sameWGWorld (copy : Bool) (e ck hash : List UInt8) :
    SameView (id : WGWorld → WGWorld) (messageEphemeral copy e ck hash) := by
  unfold messageEphemeral
  apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branch .msgEphemeralCopy _) (fun w => w = k))
  intro _
  apply SameView.bind (kdf_sameWGWorld _ _ _ _)
  intro outs
  exact SameView.bind (kdfOut_sameWGWorld _ _) (fun _ => SameView.pure _ _)

theorem mixDh_sameWGWorld (key : Bool) (ck priv pub : List UInt8) :
    SameView (id : WGWorld → WGWorld) (mixDh key ck priv pub) := by
  unfold mixDh
  apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branch .mixDhNull _) (fun w => w = k))
  intro isNull
  split
  · exact SameView.pure _ _
  · apply SameView.bind (kdf_sameWGWorld _ _ _ _)
    intro outs
    apply SameView.bind (kdfOut_sameWGWorld _ _)
    intro first
    split
    · exact SameView.bind (kdfOut_sameWGWorld _ _) (fun _ => SameView.pure _ _)
    · exact SameView.bind (SameView.pure _ _) (fun _ => SameView.pure _ _)

theorem mixPrecomputedDh_sameWGWorld (ck precomputed : List UInt8) :
    SameView (id : WGWorld → WGWorld) (mixPrecomputedDh ck precomputed) := by
  unfold mixPrecomputedDh
  apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branch .mixPrecomputedNull _) (fun w => w = k))
  intro isNull
  split
  · exact SameView.pure _ _
  · apply SameView.bind (kdf_sameWGWorld _ _ _ _)
    intro outs
    apply SameView.bind (kdfOut_sameWGWorld _ _)
    intro first
    exact SameView.bind (kdfOut_sameWGWorld _ _) (fun _ => SameView.pure _ _)

theorem messageDecrypt_sameWGWorld (sealed key hash : List UInt8) :
    SameView (id : WGWorld → WGWorld) (messageDecrypt sealed key hash) := by
  unfold messageDecrypt
  apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branch .msgDecryptFailed _) (fun w => w = k))
  intro failed
  split
  · exact SameView.pure _ _
  · split
    · exact SameView.pure _ _
    · exact fun k => hoare_liftAmbient (AmbientM.invariant _) (fun w => w = k)

end Leanux.Proofs.Framing
