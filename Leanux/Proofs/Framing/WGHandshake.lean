import Leanux.Proofs.Framing.Tools
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
  mvcgen [generatePublic, branch, AmbientM.branch]

theorem kdf_sameWGWorld (second third : Bool) (chainingKey data : List UInt8) :
    SameView (id : WGWorld → WGWorld) (kdf second third chainingKey data) := by
  apply SameView.of_wp
  intro k
  mvcgen [kdf, WG.orM, branch, AmbientM.branch]

theorem kdfOut_sameWGWorld (outs : List (List UInt8)) (i : Nat) :
    SameView (id : WGWorld → WGWorld) (kdfOut outs i) := by
  apply SameView.of_wp
  intro k
  mvcgen [kdfOut, invariant, AmbientM.invariant]

theorem messageEphemeral_sameWGWorld (copy : Bool) (e ck hash : List UInt8) :
    SameView (id : WGWorld → WGWorld) (messageEphemeral copy e ck hash) := by
  apply SameView.of_wp
  intro k
  have hk := fun second third ck data => (kdf_sameWGWorld second third ck data).wp (fun s => s = k)
  have ho := fun outs i => (kdfOut_sameWGWorld outs i).wp (fun s => s = k)
  mvcgen [messageEphemeral, hk, ho, branch, AmbientM.branch]

theorem mixDh_sameWGWorld (key : Bool) (ck priv pub : List UInt8) :
    SameView (id : WGWorld → WGWorld) (mixDh key ck priv pub) := by
  apply SameView.of_wp
  intro k
  have hk := fun second third ck data => (kdf_sameWGWorld second third ck data).wp (fun s => s = k)
  have ho := fun outs i => (kdfOut_sameWGWorld outs i).wp (fun s => s = k)
  mvcgen [mixDh, hk, ho, branch, AmbientM.branch]

theorem mixPrecomputedDh_sameWGWorld (ck precomputed : List UInt8) :
    SameView (id : WGWorld → WGWorld) (mixPrecomputedDh ck precomputed) := by
  apply SameView.of_wp
  intro k
  have hk := fun second third ck data => (kdf_sameWGWorld second third ck data).wp (fun s => s = k)
  have ho := fun outs i => (kdfOut_sameWGWorld outs i).wp (fun s => s = k)
  mvcgen [mixPrecomputedDh, hk, ho, branch, AmbientM.branch]

theorem messageDecrypt_sameWGWorld (sealed key hash : List UInt8) :
    SameView (id : WGWorld → WGWorld) (messageDecrypt sealed key hash) := by
  apply SameView.of_wp
  intro k
  mvcgen [messageDecrypt, branch, AmbientM.branch, invariant, AmbientM.invariant]

end Leanux.Proofs.Framing
