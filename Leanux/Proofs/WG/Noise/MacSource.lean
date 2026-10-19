import Leanux.Proofs.WG.Noise.CreationTagFrames
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGDump

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

/-- The original MAC call's single peer write is its only native state effect.
The clock test keeps its recorded inputs, short circuit and possible Stop. -/
theorem addMacToPacket_preserves (pid : PeerId) (msg : List UInt8) (P : WGWorld → Prop)
    (write : ∀ p : Peer,
      Ensures (setPeer pid {p with
        lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)),
        haveSentMac1 := true})
        (fun g => P g ∧ peerAt g pid = some p) (fun _ => P)) :
    Ensures (addMacToPacket pid msg) P (fun _ => P) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a y v b h run; cases run; exact h
  have htest (p : Peer) :
      Ensures (WG.andM (branch .addMacCookieValid p.cookieIsValid)
        (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·)))
        P (fun _ => P) := by
    apply (ensures_iff _ P (fun _ => P)).mpr
    exact (DumpComposition.andM_sameView _ _
      (fun initial => hoare_liftAmbient (AmbientM.branch .addMacCookieValid p.cookieIsValid)
        (fun (g : WGWorld) => g = initial))
      (branchExpired_sameWGWorld _ _ _ (!·))).wp P
  unfold addMacToPacket
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p
  dsimp only
  refine ensures_bind (Q := fun _ => P) _ _ (write p) (fun _ => ?_)
  refine ensures_bind _ _ (htest p) ?_
  intro accepted
  split <;> exact hpure _

end Leanux.Proofs.WG.Noise

